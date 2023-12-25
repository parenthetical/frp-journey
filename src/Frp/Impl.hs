{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

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

data Impl

type Subscriber a = Maybe a -> IO ()
type Unsubscribe = IO ()
type Invalidator = IO ()

-- | The root event 'rootTickE' has an occurrence whenever any event might have one. The
-- 'propagateRoot' action causes the root event to propagate with a unit-valued occurrence.
{-# NOINLINE rootTickE #-}
{-# NOINLINE propagateRoot #-}
rootTickE :: Event Impl ()
propagateRoot :: IO ()
(rootTickE, propagateRoot) = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  pure (eCached, doPropagate (Just ()))

instance Frp Impl where
  -- | Events are subscribed to with a callback called whenever the event has a known
  -- (non)-occurrence. Subscribing to an event returns an unsubscribe action. Unsubscribing
  -- immediately stops any callbacks from happening.
  newtype Event Impl a = Event { subscribe :: Subscriber a -> IO Unsubscribe }
  -- | Behaviors are sampling functions which are passed an optional invalidator. This invalidator
  -- is run when the Behavior's value might change (but it could also stay the same).
  newtype Behavior Impl a = Behavior (ReaderT (Maybe Invalidator) IO a)
    deriving (Functor, Applicative, Monad, MonadFix)

  type Moment Impl = IO

  -- | Never is implemented by filtering out all occurences from the root event.
  never :: Event Impl a
  never = undefined <$ FRP.filterE (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f e = cacheEvent $ Event $ \propagate -> subscribe e $ propagate <=< fmap join . mapM f

  -- | When the outer event is known to not have an occurrence, propagate non-occurrence. Otherwise,
  -- subscribe to the inner occurrence and queue-up its unsubscribe action.  It's possible to write
  -- the implementation so that unsubscribing happens immediately but using the queue made things
  -- more succinct.
  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence e = cacheEvent $ Event $ \propagate -> do
    subscribe e $ maybe (propagate Nothing) (addToEnvQueue toClearQueueRef <=< (`subscribe` propagate))

  -- | Subscribe to both merge inputs and cache the occurrences. When both (non-)occurrences are
  -- known, propagate and clear the caches.
  merge :: forall a b. Event Impl a -> Event Impl b -> Event Impl (These a b)
  merge a b = cacheEvent $ Event $ \propagate -> do
    aOccRef <- newIORef Nothing
    bOccRef <- newIORef Nothing
    let doSub :: forall c. IORef (Maybe (Maybe c)) -> Event Impl c -> IO Unsubscribe
        doSub occRef e = subscribe e $ \occ -> do
            writeIORef occRef . Just $ occ
            -- Check if we have both inputs when any input is called. If yes, clear caches and
            -- propagate.
            mapM_ (\occRes -> do
                      writeIORef aOccRef Nothing
                      writeIORef bOccRef Nothing
                      propagate occRes)
              =<< liftA2 align <$> readIORef aOccRef <*> readIORef bOccRef
    (>>) <$> doSub aOccRef a <*> doSub bOccRef b

  -- | Switch keeps the unsubscribe to the inner event in an 'IORef (Maybe Unsubscribe)'. As long as
  -- the result event of switch is subscribed to the IORef is kept as Just Unsubscribe. On
  -- unsubscribing it's set to Nothing. When switchParent's invalidator is run the old inner event
  -- is unsubscribed from and the IORef set to the new one. The invalidator only runs if the IORef
  -- is Just-valued still.
  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (Behavior switchParent) = cacheEvent $ Event $ \propagate -> mdo
    maybeUnsubscribeInnerERef <- newIORef <=< fix $ \f ->
      fmap Just . (`subscribe` propagate)
      <=< runReaderT switchParent . Just
      $ readIORef maybeUnsubscribeInnerERef >>= mapM_ (>> (f >>= writeIORef maybeUnsubscribeInnerERef))
    pure $ readIORef maybeUnsubscribeInnerERef >>= mapM_ (>> writeIORef maybeUnsubscribeInnerERef Nothing)

data BehaviorAssignment where
  BehaviorAssignment :: IORef a -> a -> IORef [Invalidator] -> BehaviorAssignment

instance MonadMoment Impl IO where
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = do
    invsRef <- newIORef []
    valRef <- newIORef v0
    -- Make sure not to touch 'e' eagerly, instead wait for Behavior init time.
    addToEnvQueue behaviorInitsRef $ void $ subscribe e $
      mapM_ (\a -> addToEnvQueue behaviorAssignmentsRef $ BehaviorAssignment valRef a invsRef)
    pure $ Behavior $ ReaderT $ \invalidator -> do
      mapM_ (modifyIORef invsRef . (:)) invalidator
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = FRP.headE rootTickE

  sample :: Behavior Impl a -> Moment Impl a
  sample (Behavior b) = do
    res <- unsafeInterleaveIO . runReaderT b $ Nothing
    addToEnvQueue behaviorInitsRef $ void . evaluate $ res
    pure res

  liftMoment :: Moment Impl a -> IO a
  liftMoment = id

managedSubscribersEvent :: IO (Event Impl a, Maybe a -> IO ())
managedSubscribersEvent = do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  pure
    ( Event $ \propagate -> do
        thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
        modifyIORef subscribersRef $ IntMap.insert thisSubId propagate
        -- If occRef is already Just we have to propagate on subscribe
        -- because the subscription on e has already propagated:
        mapM_ propagate =<< readIORef occRef
        pure $ do
          old <- readIORef subscribersRef
          unless (IntMap.member thisSubId old) $ error "managedSubscribers unsubscribed twice"
          modifyIORef subscribersRef (IntMap.delete thisSubId)
    , \occ -> do
        writeAndScheduleClear occRef occ
        mapM_ ($ occ) =<< readIORef subscribersRef
    )

cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  void . subscribe e $ doPropagate
  pure eCached

type MakeEventTrigger a = (a -> EventTrigger)
type EventTrigger = IO ()

newEvent :: IO (MakeEventTrigger a, Event Impl a)
newEvent = do
  occRef <- newIORef Nothing -- Root event (non-)occurrence is always "known", thus Maybe a
  pure (writeAndScheduleClear occRef, mapMaybeMoment (const (readIORef occRef)) rootTickE)

subscribeEvent :: forall a. Event Impl a -> IO (IORef (Maybe a))
subscribeEvent e = do
  occRef :: IORef (Maybe a) <- newIORef Nothing
  _ <- subscribe e $ mapM_ (writeAndScheduleClear occRef)
  pure occRef

runFrame :: [EventTrigger] -> IO a -> IO a
runFrame triggers program = do
  let (Env { toClearQueueRef, behaviorInitsRef, behaviorAssignmentsRef }) = theEnv
  sequence_ triggers
  propagateRoot
  res <- program
  fix $ \runHoldInits -> do
    inits <- readIORef behaviorInitsRef
    unless (null inits) $ do
      writeIORef behaviorInitsRef []
      sequence_ inits
      runHoldInits
  atomicModifyIORef toClearQueueRef ([],) >>= sequence_
  atomicModifyIORef behaviorAssignmentsRef ([],)
    >>= mapM_ (\(BehaviorAssignment valRef a invalidatorsRef) -> do
                  writeIORef valRef a
                  atomicModifyIORef invalidatorsRef ([],) >>= sequence_)
  flip unless (error "queues were not empty after runFrame")
    . and =<< sequence [ null <$> readIORef behaviorInitsRef
                       , null <$> readIORef toClearQueueRef
                       , null <$> readIORef behaviorAssignmentsRef
                       ]
  pure res

writeAndScheduleClear :: IORef (Maybe a) -> a -> IO ()
writeAndScheduleClear occRef a = do
  prev <- readIORef occRef
  when (isJust prev) $ error "occRef written twice---loop?"
  writeIORef occRef (Just a)
  addToEnvQueue toClearQueueRef $ writeIORef occRef Nothing

data Env = Env
  { toClearQueueRef :: IORef [IO ()]
  , behaviorInitsRef :: IORef [IO ()]
  , behaviorAssignmentsRef :: IORef [BehaviorAssignment]
  }

{-# NOINLINE theEnv #-}
theEnv :: Env
theEnv = unsafePerformIO $ Env <$> newIORef [] <*> newIORef [] <*> newIORef []

addToEnvQueue :: (Env -> IORef [a]) -> a -> IO ()
addToEnvQueue selector a = modifyIORef (selector theEnv) (a:)
