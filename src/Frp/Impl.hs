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

type Subscriber a = Unsubscribe -> Maybe a -> IO ()
type Unsubscribe = IO ()
type Invalidator = IO ()

subscribe' :: Event Impl a -> (Maybe a -> IO ()) -> IO ()
subscribe' e f = subscribe e (const f)

instance Frp Impl where
  -- | Events are subscribed to with a callback which runs whenever
  -- the event has a known (non)-occurrence. Subscribing to an event
  -- returns both an unsubscribe action, which when called guarantees
  -- that the callback will stop receiving occurrences, and wether an
  -- occurrence is known for the current frame. If the occurrence is
  -- already known the callback is not called.
  newtype Event Impl a = Event { subscribe :: Subscriber a -> IO () }
  -- | Behaviors are sampling functions which are passed an optional
  -- "invalidator". This invalidator is run when the Behavior's value
  -- might be changing.
  newtype Behavior Impl a = Behavior (ReaderT (Maybe Invalidator) IO a)
    deriving (Functor, Applicative, Monad, MonadFix)
  type Moment Impl = IO

  never :: Event Impl a
  never = undefined <$ FRP.filterE (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f e = cacheEvent $ Event $ \propagate -> subscribe e $ \unsubscribe -> propagate unsubscribe <=< fmap join . mapM f

  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence coincidenceParent = cacheEvent $ Event $ \propagate' -> do
    subscribe coincidenceParent $ \unsubscribeOuter ->
      let propagate = propagate' unsubscribeOuter
      in maybe (propagate Nothing) (`subscribe` \unsubscribeInner occ -> unsubscribeInner >> propagate occ)

  merge :: forall a b. Event Impl a -> Event Impl b -> Event Impl (These a b)
  merge a b = cacheEvent $ Event $ \propagate -> do
    aOccRef <- newIORef Nothing
    bOccRef <- newIORef Nothing
    aUnsubscribeRef <- newIORef $ error "aUnsubscribe uninitialized"
    bUnsubscribeRef <- newIORef $ error "bUnsubscribe uninitialized"
    let doSub :: forall c. IORef (Maybe (Maybe c)) -> IORef Unsubscribe -> Event Impl c -> IO ()
        doSub occRef unsubscribeRef e = subscribe e $ \unsubscribe -> unsafePerformIO $ do
          writeIORef unsubscribeRef unsubscribe
          pure $ \occ -> do
            writeIORef occRef . Just $ occ
            mapM_ (\occRes -> do
                      writeIORef aOccRef Nothing >> writeIORef bOccRef Nothing
                      propagate (join (readIORef aUnsubscribeRef) >> join (readIORef bUnsubscribeRef)) occRes)
              =<< liftA2 align <$> readIORef aOccRef <*> readIORef bOccRef
    doSub aOccRef aUnsubscribeRef a
    doSub bOccRef bUnsubscribeRef b

  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (Behavior switchParent) = cacheEvent $ Event $ \propagate -> do
    maybeUnsubscribeInnerERef <- newIORef $ error "unsubscribeInnerERef uninitialized"
    fix $ \f ->
      runReaderT switchParent (Just $ mapM_ (>> f) =<< readIORef maybeUnsubscribeInnerERef)
      >>= (`subscribe` \unsubscribeInnerE -> unsafePerformIO $ do
              writeIORef maybeUnsubscribeInnerERef (Just unsubscribeInnerE)
              pure $ propagate (writeIORef maybeUnsubscribeInnerERef Nothing >> unsubscribeInnerE))

data BehaviorAssignment where
  BehaviorAssignment :: IORef a -> a -> IORef [Invalidator] -> BehaviorAssignment

instance MonadMoment Impl IO where
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = do
    invsRef <- newIORef []
    valRef <- newIORef v0
    -- Make sure not to touch 'e' eagerly, instead wait for Behavior init time.
    addToQueue behaviorInitsRef $ void $ subscribe' e $
      mapM_ (\a -> addToQueue behaviorAssignmentsRef $ BehaviorAssignment valRef a invsRef)
    pure $ Behavior $ ReaderT $ \maybeInvalidator -> do
      mapM_ (addToQueue invsRef) maybeInvalidator
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = FRP.headE rootTickE

  sample :: Behavior Impl a -> Moment Impl a
  sample (Behavior b) = do
    res <- unsafeInterleaveIO . runReaderT b $ Nothing
    addToQueue behaviorInitsRef $ void . evaluate $ res
    pure res

-- | The root event
{-# NOINLINE _root #-}
_root :: (Event Impl (), IO ())
_root@(rootTickE, propagateRoot) = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  pure (eCached, doPropagate (Just ()))

managedSubscribersEvent :: IO (Event Impl a, Maybe a -> IO ())
managedSubscribersEvent = do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  pure
    ( Event $ \propagate -> do
        thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
        let propagate' = propagate $ do
             old <- readIORef subscribersRef
             unless (IntMap.member thisSubId old) $ error "managedSubscribers unsubscribed twice"
             modifyIORef subscribersRef (IntMap.delete thisSubId)
        modifyIORef subscribersRef $ IntMap.insert thisSubId propagate'
        -- If occRef is already Just we have to propagate on subscribe
        -- because the subscription on e has already propagated:
        mapM_ propagate' =<< readIORef occRef
    , \occ -> do
        writeAndScheduleClear "managedSubscribers" occRef occ
        mapM_ ($ occ) =<< readIORef subscribersRef
    )

cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  void . subscribe' e $ doPropagate
  pure eCached

type MakeEventTrigger a = (a -> EventTrigger)
type EventTrigger = IO ()

newEvent :: IO (MakeEventTrigger a, Event Impl a)
newEvent = do
  occRef <- newIORef Nothing -- Root event (non-)occurrence is always "known", thus Maybe a
  pure (writeAndScheduleClear "newEvent" occRef, mapMaybeMoment (const (readIORef occRef)) rootTickE)

subscribeEvent :: forall a. Event Impl a -> IO (IORef (Maybe a))
subscribeEvent e = do
  -- TODO: add extra safety by having (Maybe (Maybe a))? This would
  -- notify the user that they tried to read an event occurrence
  -- outside of a frame. Maybe subscribeEvent should return a read action which throws an exception.
  occRef :: IORef (Maybe a) <- newIORef Nothing
  _ <- subscribe' e $ mapM_ (writeAndScheduleClear "subscribeEvent" occRef)
  pure occRef

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

writeAndScheduleClear :: String -> IORef (Maybe a) -> a -> IO ()
writeAndScheduleClear name occRef a = do
  prev <- readIORef occRef
  when (isJust prev) $ error $ "occRef written twice---loop? -- " <> name
  writeIORef occRef (Just a)
  addToQueue toClearQueueRef (Some (Compose occRef))

addToQueue :: IORef [a] -> a -> IO ()
addToQueue q = modifyIORef q . (:)

{-# NOINLINE toClearQueueRef #-}
toClearQueueRef :: IORef [Some (Compose IORef Maybe)]
toClearQueueRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorAssignmentsRef #-}
behaviorAssignmentsRef :: IORef [BehaviorAssignment]
behaviorAssignmentsRef = unsafePerformIO $ newIORef []

{-# NOINLINE behaviorInitsRef #-}
behaviorInitsRef :: IORef [IO ()]
behaviorInitsRef = unsafePerformIO $ newIORef []
