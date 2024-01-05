{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Frp.Impl
(newEvent, subscribeEvent, runFrame, Impl, MomentImpl(..), EventTrigger, ReadTime, readBehavior)
where

import Prelude hiding (filter)
import Frp.Class
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
import Control.Monad.IO.Class (MonadIO)
import Witherable

data Impl

type Subscriber a = Maybe a -> IO ()
type Unsubscribe = IO ()
type Invalidator = IO ()

-- | The root event 'rootTickE' has an occurrence whenever any event might have one.
{-# NOINLINE rootTickE #-}
rootTickE :: Event Impl ()
-- | The 'propagateRoot' action causes the root event to propagate with a unit-valued occurrence.
{-# NOINLINE propagateRoot #-}
propagateRoot :: IO ()
(rootTickE, propagateRoot) = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  pure (eCached, doPropagate (Just ()))

newtype MomentImpl a = MomentImpl { runMomentImpl :: IO a }
  deriving (Functor,Applicative,Monad,MonadFix, MonadIO)

-- | 
instance Frp Impl where
  -- Events are subscribed to with a callback called whenever the event has a known
  -- (non)-occurrence. Subscribing to an event returns an unsubscribe action. Unsubscribing
  -- immediately stops any callbacks from happening.
  newtype Event Impl a = EventI { subscribe :: Subscriber a -> IO Unsubscribe }
  -- Behaviors are sampling functions which are passed an optional invalidator. This invalidator
  -- is run when the Behavior's value might change (but it could also stay the same).
  newtype Behavior Impl a = BehaviorI (ReaderT (Maybe Invalidator) IO a)
    deriving (Functor, Applicative, Monad, MonadFix)

  type Moment Impl = MomentImpl

  -- Never is implemented by filtering out all occurences from the root event.
  never :: Event Impl a
  never = undefined <$ filter (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f e = cacheEvent $ EventI $ \propagate ->
    subscribe e $ propagate <=< fmap join . mapM (runMomentImpl . f)

  -- When the outer event is known to not have an occurrence, propagate non-occurrence. Otherwise,
  -- subscribe to the inner occurrence and queue-up its unsubscribe action.  It's possible to write
  -- the implementation so that unsubscribing happens immediately but using the queue made things
  -- more succinct.
  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence e = cacheEvent $ EventI $ \propagate ->
    subscribe e $ maybe (propagate Nothing) (addToEnvQueue toClearQueueRef <=< (`subscribe` propagate))

  -- Subscribe to both merge inputs and cache the occurrences. When both (non-)occurrences are
  -- known, propagate and clear the caches.
  merge :: forall a b. Event Impl a -> Event Impl b -> Event Impl (These a b)
  merge a b = cacheEvent $ EventI $ \propagate -> do
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

  -- Switch keeps the unsubscribe to the inner event in an 'IORef (Maybe Unsubscribe)'. As long as
  -- the result event of switch is subscribed to the IORef is kept as Just Unsubscribe. On
  -- unsubscribing it's set to Nothing. When switchParent's invalidator is run the old inner event
  -- is unsubscribed from and the IORef set to the new one. The invalidator only runs if the IORef
  -- is Just-valued still.
  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (BehaviorI switchParent) = cacheEvent $ EventI $ \propagate -> mdo
    maybeUnsubscribeInnerERef <- newIORef <=< fix $ \f ->
      fmap Just . (`subscribe` propagate)
      <=< runReaderT switchParent . Just
      $ readIORef maybeUnsubscribeInnerERef >>= mapM_ (>> (f >>= writeIORef maybeUnsubscribeInnerERef))
    pure $ readIORef maybeUnsubscribeInnerERef >>= mapM_ (>> writeIORef maybeUnsubscribeInnerERef Nothing)

  -- Hold returns a behavior which is initialized at behavior init time and changes at behavior
  -- assignment time. Whenever the behavior is read an invalidator action can be added which is
  -- called when the behavior changes.
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = MomentImpl $ do
    invsRef <- newIORef [] -- The list of invalidators that have to run whenever the result behavior
                           -- changes.
    valRef <- newIORef v0
    -- Make sure not to touch 'e' eagerly, instead wait for Behavior init time.
    addToEnvQueue behaviorInitsRef $ void $ subscribe e $
      mapM_ (\a -> addToEnvQueue behaviorAssignmentsRef $ BehaviorAssignment valRef a invsRef)
    pure $ BehaviorI $ ReaderT $ \invalidator -> do
      mapM_ (modifyIORef invsRef . (:)) invalidator
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = headE rootTickE

  -- Sample takes extra care to be lazy by delaying the evaluation of the sampled behavior.  The
  -- last moment by which the sample would need to be forced is behavior invalidation time, but here
  -- I've forced the evaluation at the next behavior init time.
  sample :: Behavior Impl a -> Moment Impl a
  sample (BehaviorI b) = MomentImpl $ do
    res <- unsafeInterleaveIO $ runReaderT b Nothing
    addToEnvQueue behaviorInitsRef $ void . evaluate $ res
    pure res

data BehaviorAssignment where
  BehaviorAssignment :: IORef a -> a -> IORef [Invalidator] -> BehaviorAssignment


-- | Returns an event which can have multiple subscribers and a propagating procedure. The propagator
-- is not allowed to be called outside of a frame (this is unenforced)!
managedSubscribersEvent :: IO (Event Impl a, Maybe a -> IO ())
managedSubscribersEvent = do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  pure
    ( EventI $ \propagate -> do
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

-- | Cache event occurrences.
cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ do
  (eCached, doPropagate) <- managedSubscribersEvent
  void . subscribe e $ doPropagate
  pure eCached

newtype EventTrigger = EventTrigger { runEventTrigger :: IO () }

-- | Create a new event. Returns a "make trigger" function to which you can pass an occurrence value
-- and obtain an 'EventTrigger' for use with 'runFrame', and the new event.
newEvent :: IO (a -> EventTrigger, Event Impl a)
newEvent = do
  occRef <- newIORef Nothing -- Root event (non-)occurrence is always "known", thus Maybe a
  pure (EventTrigger . writeAndScheduleClear occRef, mapMaybeMoment (const (MomentImpl $ readIORef occRef)) rootTickE)

-- | Subscribe to an event to obtain an "read occurrence" action which will contain the event
-- occurrence value when read inside the 'program' argument of 'runFrame'.
subscribeEvent :: forall a. Event Impl a -> IO (ReadTime (Maybe a))
subscribeEvent e = do
  occRef :: IORef (Maybe (Maybe a)) <- newIORef Nothing
  _ <- subscribe e $ writeAndScheduleClear occRef
  pure $ ReadTime $ fromMaybe (error "Occurrence read outside of runFrame?") <$> readIORef occRef

newtype ReadTime a = ReadTime { runReadTime :: IO a }
  deriving (Functor,Applicative,Monad)

readBehavior :: Behavior Impl a -> ReadTime a
readBehavior (BehaviorI b) = ReadTime $ runReaderT b Nothing

-- | Inside the second argument you can read Behaviors and read event occurrences after subscribing
-- to an event.
runFrame :: [EventTrigger] -> ReadTime a -> IO a
runFrame triggers program = do
  let (Env { toClearQueueRef, behaviorInitsRef, behaviorAssignmentsRef }) = theEnv
  mapM_ runEventTrigger triggers
  propagateRoot
  res <- runReadTime program
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

-- | Write a value to an event occurrence cache/IORef and schedule it to be cleared.
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
