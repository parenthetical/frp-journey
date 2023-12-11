{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | The rules for this implementation are: an event can only receive a propagation once per time frame, and if its occurrence is known on subscription it will never propagate.

module Frp.Impl
(newEvent, subscribeEvent, runFrame, Impl)
where

import Frp.Class
import qualified Frp.Class as FRP
import Control.Monad.Fix
import Control.Monad
import Data.IORef
import Data.Align (Semialign(..))
import Data.These
import Data.Maybe (isJust)
import System.IO.Unsafe ( unsafePerformIO, unsafeInterleaveIO )
import qualified Data.IntMap as IntMap
import Control.Monad.Reader (ReaderT(..))
import GHC.IO (evaluate)
import Data.Functor.Compose
import Data.Some

data Impl

newtype Subscriber a = Subscriber { subscriberPropagate :: Maybe a -> IO () }
type Unsubscribe = IO ()
type Invalidator = IO ()

instance Frp Impl where
  -- | Events are subscribed to with a callback which runs whenever
  -- the event has a known (non)-occurrence. Subscribing to an event
  -- returns both an unsubscribe action, which when called guarantees
  -- that the callback will stop receiving occurrences, and wether an
  -- occurrence is known for the current frame. If the occurrence is
  -- already known the callback is not called.
  newtype Event Impl a = Event
    { subscribeAndRead :: Subscriber a -> IO (Unsubscribe, Maybe (Maybe a)) }
  -- | Behaviors are sampling functions which are passed an optional
  -- "invalidator". This invalidator is run when the Behavior's value
  -- might be changing.
  newtype Behavior Impl a = Behavior (ReaderT (Maybe Invalidator) IO a)
    deriving (Functor, Applicative, Monad, MonadFix)
  type Moment Impl = IO

  never :: Event Impl a
  never = undefined <$ FRP.filterE (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f = Event .  subscribeWith (fmap join . mapM f)

  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence coincidenceParent = cacheEvent $ Event $ \sub -> do
    let f = fmap join -- TODO: awkward
          . mapM (maybe
                  (pure (Just Nothing))
                  (\innerE -> fmap snd . subscribeWith'
                     (\unsubscribeInner occ -> unsubscribeInner >> pure occ) innerE
                     . Subscriber $ subscriberPropagate sub))
    (unsubscribeOuter, occOuter) <-
      subscribeAndRead coincidenceParent $ Subscriber $ mapM_ (subscriberPropagate sub) <=< f . Just
    occ <- f occOuter
    pure (unsubscribeOuter, occ)

  merge :: forall a b. Event Impl a -> Event Impl b -> Event Impl (These a b)
  merge a b = cacheEvent $ Event $ \subscriber -> mdo
    let maybeResult :: IO (Maybe (Maybe (These a b)))
        maybeResult = do
          res <- liftA2 align <$> readIORef aOccRef <*> readIORef bOccRef
          when (isJust res) $ do
            writeIORef aOccRef Nothing
            writeIORef bOccRef Nothing
          pure res
    let doSub :: forall c. Event Impl c -> IO (IO (), IORef (Maybe (Maybe c)))
        doSub e = do
          occRef <- newIORef Nothing
          (eUnsubscribe, _) <-
            subscribeWith ((Nothing <$) . writeIORef occRef . Just) e . Subscriber $ \_ ->
              mapM_ (subscriberPropagate subscriber) =<< maybeResult
          pure (eUnsubscribe, occRef)
    (aUnsubscribe, aOccRef) <- doSub a
    (bUnsubscribe, bOccRef) <- doSub b
    (aUnsubscribe >> bUnsubscribe,) <$> maybeResult

  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (Behavior switchParent) = cacheEvent $ Event $ \sub ->
    fix $ \f -> mdo
      maybeInvalidatorRef <- newIORef . Just $ unsubscribeInnerE >> void f
      e <- runReaderT switchParent $ Just $
        readIORef maybeInvalidatorRef >>= mapM_ (writeIORef maybeInvalidatorRef Nothing >>)
      (unsubscribeInnerE, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate sub
      pure (writeIORef maybeInvalidatorRef Nothing >> unsubscribeInnerE, occ)

data BehaviorAssignment where
  BehaviorAssignment :: IORef a -> a -> IORef [Invalidator] -> BehaviorAssignment

instance MonadMoment Impl IO where
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = do
    invsRef <- newIORef []
    valRef <- newIORef v0
    -- Make sure not to touch 'e' eagerly, instead wait for Behavior init time.
    addToQueue behaviorInitsRef $ void $ subscribeWith
      (mapM (\a -> addToQueue behaviorAssignmentsRef $ BehaviorAssignment valRef a invsRef))
      e
      . Subscriber $ const (pure ())
    pure $ Behavior $ ReaderT $ \invalidator -> do
      mapM_ (addToQueue invsRef) invalidator
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = FRP.headE rootTickE

  sample :: Behavior Impl a -> Moment Impl a
  sample (Behavior b) = do
    res <- unsafeInterleaveIO . runReaderT b $ Nothing
    addToQueue behaviorInitsRef $ void . evaluate $ res
    pure res

  liftMoment :: Moment Impl a -> IO a
  liftMoment = id

-- | The root event
{-# NOINLINE _root #-}
_root :: (Event Impl (), IO ())
_root@(rootTickE, propagateRoot) = unsafePerformIO $ do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  pure ( Event $ \sub -> do
           thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
           modifyIORef subscribersRef $ IntMap.insert thisSubId sub
           (modifyIORef subscribersRef (IntMap.delete thisSubId),) <$> readIORef occRef
       , do writeAndScheduleClear occRef (Just ())
            mapM_ (`subscriberPropagate` Just ()) =<< readIORef subscribersRef
       )

type MakeEventTrigger a = (a -> EventTrigger)
type EventTrigger = IO ()

newEvent :: IO (MakeEventTrigger a, Event Impl a)
newEvent = do
  occRef <- newIORef Nothing -- Root event (non-)occurrence is always "known", thus Maybe a
  let e = Event $ subscribeWith (const (readIORef occRef)) rootTickE
  pure (writeAndScheduleClear occRef, e)

subscribeEvent :: forall a. Event Impl a -> IO (IORef (Maybe a))
subscribeEvent e = do
  occRef :: IORef (Maybe a) <- newIORef Nothing
  _ <- subscribeWith (mapM (writeAndScheduleClear occRef)) e . Subscriber $ const (pure ())
  pure occRef


-- | Subscribe to an event while mapping a function over it. This is
-- mapMomentMaybe and subscribe combined. Passes the unsubscribe
-- action to 'f' without FixIO cycles.
subscribeWith' :: (Unsubscribe -> Maybe a -> IO (Maybe b)) -> Event Impl a -> Subscriber b -> IO (Unsubscribe, Maybe (Maybe b))
subscribeWith' f e subscriber = mdo
  (unsubscribe, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate subscriber <=< f unsubscribe
  fmap (unsubscribe,) .  mapM (f unsubscribe) $ occ

subscribeWith :: (Maybe a -> IO (Maybe b)) -> Event Impl a -> Subscriber b -> IO (Unsubscribe, Maybe (Maybe b))
subscribeWith f = subscribeWith' (const f)

runFrame :: [EventTrigger] -> IO a -> IO a
runFrame triggers program = do
  sequence_ triggers
  propagateRoot
  res <- program
  fix $ \runHoldInits -> do
    inits <- readIORef behaviorInitsRef
    unless (null inits) $ do
      writeIORef behaviorInitsRef []
      sequence_ inits
      runHoldInits
  atomicModifyIORef toClearQueueRef ([],) >>= mapM_ (\(Some (Compose occRef)) -> writeIORef occRef Nothing)
  atomicModifyIORef behaviorAssignmentsRef ([],)
    >>= mapM_ (\(BehaviorAssignment valRef a invalidatorsRef) -> do
                  writeIORef valRef a
                  atomicModifyIORef invalidatorsRef ([],) >>= sequence_)
  pure res

cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  void . subscribeWith (\occ -> writeAndScheduleClear occRef occ >> pure occ) e . Subscriber $ \occ ->
    mapM_ (`subscriberPropagate` occ) =<< readIORef subscribersRef
  pure $ Event $ \sub -> do
    thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
    modifyIORef subscribersRef $ IntMap.insert thisSubId sub
    (modifyIORef subscribersRef (IntMap.delete thisSubId),) <$> readIORef occRef

writeAndScheduleClear :: IORef (Maybe a) -> a -> IO ()
writeAndScheduleClear occRef a = do
  prev <- readIORef occRef
  when (isJust prev) $ error "occRef written twice---loop?"
  writeIORef occRef (Just a)
  addToQueue toClearQueueRef (Some (Compose occRef))

addToQueue :: IORef [a] -> a -> IO ()
addToQueue q a = modifyIORef q (a:)

{-# NOINLINE toClearQueueRef #-}
toClearQueueRef :: IORef [Some (Compose IORef Maybe)]
toClearQueueRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorAssignmentsRef #-}
behaviorAssignmentsRef :: IORef [BehaviorAssignment]
behaviorAssignmentsRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorInitsRef #-}
behaviorInitsRef :: IORef [IO ()]
behaviorInitsRef = unsafePerformIO $ newIORef []
