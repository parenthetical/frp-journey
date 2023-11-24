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
import Data.Maybe (isJust, fromMaybe)
import System.IO.Unsafe ( unsafePerformIO, unsafeInterleaveIO )
import qualified Data.IntMap as IntMap
import Control.Monad.Reader (ReaderT(..))
import GHC.IO (evaluate)

data Impl

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
  let e = Event $ subscribeWith rootTickE (\_ -> const (readIORef occRef))
  pure (writeAndScheduleClear occRef, e)

subscribeEvent :: forall a. Event Impl a -> IO (IORef (Maybe a))
subscribeEvent e = do
  occRef :: IORef (Maybe a) <- newIORef Nothing
  _ <- subscribeWith e (\_ occ -> mapM_ (writeAndScheduleClear occRef) occ >> pure Nothing) $ Subscriber $ const (pure ())
  pure occRef

newtype Subscriber a = Subscriber { subscriberPropagate :: Maybe a -> IO () }
type Unsubscribe = IO ()

-- TODO: MaybeT IO (Maybe b)?
subscribeWith :: Event Impl a -> (Unsubscribe -> Maybe a -> IO (Maybe b)) -> Subscriber b -> IO (Unsubscribe, Maybe (Maybe b))
subscribeWith e f subscriber = mdo
  (unsubscribe, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate subscriber <=< (unsubscribe `f`)
  fmap (unsubscribe,) .  mapM (unsubscribe `f`) $ occ

type Invalidator = IORef (Maybe (IO ()))

instance Frp Impl where
  type Moment Impl = IO
  newtype Behavior Impl a = Behavior (ReaderT Invalidator IO a)
    deriving (Functor, Applicative, Monad, MonadFix)
  newtype Event Impl a = Event
    { subscribeAndRead :: Subscriber a -> IO (Unsubscribe, Maybe (Maybe a)) }

  never :: Event Impl a
  never = undefined <$ FRP.filterE (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f = Event . (`subscribeWith` (\_ -> fmap join . mapM f))

  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence coincidenceParent = cacheEvent $ Event $ \sub -> do
    let f = fmap join
          . mapM (maybe
                  (pure (Just Nothing))
                  (\innerE -> mdo
                      fmap snd .
                        subscribeWith innerE (\unsubscribeInner occ -> do
                                                 unsubscribeInner
                                                 pure occ)
                        $ Subscriber $ subscriberPropagate sub))
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
          (eUnsubscribe, _eOcc) <-
            subscribeWith e (\_ occ -> writeIORef occRef (Just occ) >> pure Nothing) $ Subscriber $ \_ ->
              mapM_ (subscriberPropagate subscriber) =<< maybeResult
          pure (eUnsubscribe, occRef)
    (aUnsubscribe, aOccRef) <- doSub a
    (bUnsubscribe, bOccRef) <- doSub b
    (aUnsubscribe >> bUnsubscribe,) <$> maybeResult

  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (Behavior switchParent) = cacheEvent $ Event $ \sub ->
    fix $ \f -> mdo
      maybeInvalidator <- newIORef . Just $ unsubscribeInnerE >> void f
      e <- runReaderT switchParent maybeInvalidator
      (unsubscribeInnerE, occ) <- subscribeAndRead e $ Subscriber $ subscriberPropagate sub
      pure (writeIORef maybeInvalidator Nothing >> unsubscribeInnerE, occ)

instance MonadMoment Impl IO where
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = do
    invsRef <- newIORef []
    valRef <- newIORef v0
    addToQueue behaviorInitsRef $ void $ subscribeWith e
      (const (mapM (\a -> addToQueue behaviorAssignmentsRef $ do
                       writeIORef valRef a
                       atomicModifyIORef invsRef ([],) >>=
                         -- TODO: confusing code, make more obvious (the join in particular):
                         mapM_ (join . (`atomicModifyIORef` (\i -> (Nothing, fromMaybe (pure ()) i)))))))
      $ Subscriber $ const (pure ())
    pure $ Behavior $ ReaderT $ \invalidator -> do
      addToQueue invsRef invalidator
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = FRP.headE rootTickE

  sample :: Behavior Impl a -> Moment Impl a
  sample (Behavior b) = do
    res <- unsafeInterleaveIO . runReaderT b =<< newIORef Nothing
    addToQueue behaviorInitsRef $ void . evaluate $ res
    pure res

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
  -- TODO: write IORefs to queue
  atomicModifyIORef toClearQueueRef ([],) >>= sequence_
  atomicModifyIORef behaviorAssignmentsRef ([],) >>= sequence_
  pure res

cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  void . subscribeWith e (\_ occ -> writeAndScheduleClear occRef occ >> pure occ) $ Subscriber $ \occ ->
    mapM_ (`subscriberPropagate` occ) =<< readIORef subscribersRef
  pure $ Event $ \sub -> do
    thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
    modifyIORef subscribersRef $ IntMap.insert thisSubId sub
    (modifyIORef subscribersRef (IntMap.delete thisSubId),) <$> readIORef occRef
  
writeAndScheduleClear :: IORef (Maybe a) -> a -> IO ()
writeAndScheduleClear occRef a = do
  prev <- readIORef occRef
  when (isJust prev) $ do
    error "occRef written twice"
  writeIORef occRef (Just a)
  addToQueue toClearQueueRef (writeIORef occRef Nothing)

addToQueue :: IORef [a] -> a -> IO ()
addToQueue q a = modifyIORef q (a:)

{-# NOINLINE toClearQueueRef #-}
toClearQueueRef :: IORef [a]
toClearQueueRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorAssignmentsRef #-}
behaviorAssignmentsRef :: IORef [IO ()]
behaviorAssignmentsRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorInitsRef #-}
behaviorInitsRef :: IORef [IO ()]
behaviorInitsRef = unsafePerformIO $ newIORef []
