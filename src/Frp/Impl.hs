{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Description: An implementation of FRP via graph traversal.

The implementation performs a number of actions for every "frame".  A frame is a single logical
point in time at which any events might be occurring (including none occurring).  The full driving
algorithm can be seen in the 'runFrame' function.

First, a graph traversal algorithm visits every event to compute whether it occurs or not.  This
occurrence value is of a 'Maybe' type, where 'Nothing' signifies no occurrence.  The actual
traversal is embedded in the implementation of the combinators rather than having this concern
separated out.

While traversing, IO actions are enqueued to take care of caching occurrences and unsubscribing
(with 'postTraversalQueueRef'), as well as taking care of behavior initialization and updates (via
the 'behaviorInitsRef' and 'behaviorAssignmentsRef' queues).

After graph traversal, the various queues are processed and emptied.
-}
module Frp.Impl
(newEvent, subscribeEvent, runFrame, Impl, EventTrigger, ReadTime, readBehavior, unsubscribe)
where

import Prelude hiding (filter)
import Frp.Class
import Control.Monad.Fix
import Control.Monad
import Data.IORef
import Data.Align (Semialign(..))
import Data.These
import Data.Maybe (fromMaybe, isJust)
import System.IO.Unsafe ( unsafePerformIO, unsafeInterleaveIO )
import qualified Data.IntMap as IntMap
import Control.Monad.Reader (ReaderT(..))
import GHC.IO (evaluate)
import Witherable
import Data.Foldable (for_)
import System.Mem.Weak (deRefWeak, mkWeakPtr, finalize)
import GHC.Base (Any)
import Unsafe.Coerce (unsafeCoerce)
import GHC.Weak (Weak)

data Impl

type Propagator a = Maybe a -> IO ()

data Subscription = Subscription { unsubscribe :: IO (), _keepAlive :: {-# NOUNPACK #-} Any }

instance Semigroup Subscription where
  Subscription a a' <> Subscription b b' = Subscription (a >> b) (unsafeCoerce (a',b'))

type Invalidator = IO ()

type SubscribersRef a = IORef (IntMap.IntMap (Weak (IORef (Propagator a))))

-- | The root event 'rootTickE' has an occurrence whenever any event might have one.
{-# NOINLINE rootTickE #-}
rootTickE :: Event Impl ()
-- | The 'propagateRoot' action causes the root event to propagate with a unit-valued occurrence.
{-# NOINLINE propagateRoot #-}
propagateRoot :: IO ()
_rootSubscribersRef :: SubscribersRef ()
(rootTickE, propagateRoot, _rootSubscribersRef) = unsafePerformIO $ do
  (eCached, doPropagate, subscribersRef) <- managedSubscribersEvent $ do
    putStrLn "root init"
    pure $ putStrLn "root de-init"
  pure (eCached, doPropagate (Just ()), subscribersRef)

-- | 
instance Frp Impl where
  -- Events are subscribed to with a callback called whenever the event has a known
  -- (non)-occurrence. Subscribing to an event returns a Subscription value which needs to be
  -- retained in its entirety to keep the callback being called on an occurrences unsubscribing
  -- stops callbacks from happening. It is not well defined wether you might still receive one for
  -- the current time after unsubscribing.
  newtype Event Impl a = EventI { subscribe :: Propagator a -> IO Subscription }
  -- Behaviors are sampling functions which are passed an optional invalidator. This invalidator is
  -- run when the Behavior's value might change (but it could also stay the same).  Behaviors also
  -- implement a Writer Monad via a list-valued IORef. This serves to keep the subscriptions to the
  -- events which influence the behavior's value alive. Pass in an IORef and keep it alive if you
  -- depend on receiving updates from a Behavior (via it calling your invalidator).
  newtype Behavior Impl a = BehaviorI (ReaderT (Maybe (Weak Invalidator, IORef [IORef (Maybe Subscription)])) IO a)
    deriving (Functor, Applicative, Monad, MonadFix)

  type Moment Impl = IO

  -- Never is implemented by filtering out all occurences from the root event.
  never :: Event Impl a
  never = undefined <$ filter (const False) rootTickE

  mapMaybeMoment :: (a -> Moment Impl (Maybe b)) -> Event Impl a -> Event Impl b
  mapMaybeMoment f e = cacheEvent $ EventI $ \propagate ->
    subscribe e $ propagate <=< fmap join . mapM f

  -- When the outer event is known to not have an occurrence, propagate non-occurrence. Otherwise,
  -- subscribe to the inner occurrence and queue-up its unsubscribe action.  It's possible to write
  -- the implementation so that unsubscribing happens immediately but using the queue made things
  -- more succinct.
  coincidence :: Event Impl (Event Impl a) -> Event Impl a
  coincidence e = cacheEvent $ EventI $ \propagate ->
    subscribe e $ maybe (propagate Nothing) (addToEnvQueue postTraversalQueueRef . unsubscribe <=< (`subscribe` propagate))

  -- Subscribes to both merge inputs and cache the occurrences. When both (non-)occurrences are
  -- known, propagate and clear the caches. Unsubscribing unsubscribes from both input events.
  merge :: forall a b. Event Impl a -> Event Impl b -> Event Impl (These a b)
  merge a b = cacheEvent $ EventI $ \propagate -> do
    aOccRef <- newIORef Nothing
    bOccRef <- newIORef Nothing
    let doSub :: forall c. IORef (Maybe (Maybe c)) -> Event Impl c -> IO Subscription
        doSub occRef e = subscribe e $ \occ -> do
            writeIORef occRef . Just $ occ
            -- Check if we have both inputs when any input is called. If yes, clear caches and
            -- propagate.
            mapM_ (\occRes -> do
                      writeIORef aOccRef Nothing
                      writeIORef bOccRef Nothing
                      propagate occRes)
              =<< liftA2 align <$> readIORef aOccRef <*> readIORef bOccRef
    (<>) <$> doSub aOccRef a <*> doSub bOccRef b

{-
  Switch keeps the subscription to the inner event in an IORef (Maybe Subscription). As long as the
  result event of switch is subscribed to the IORef is kept as Just; on unsubscribing it's set to
  Nothing. When switchParent's invalidator is run the old inner event is unsubscribed from and the
  IORef set to the new one. The invalidator only runs if the IORef is Just-valued still, so that
  unsubscribing from the resulting switch event stops new subscriptions (and semantics-breaking
  propagations) from happening.
-}
  switch :: Behavior Impl (Event Impl a) -> Event Impl a
  switch (BehaviorI switchParent) = cacheEvent $ EventI $ \propagate -> mdo
    switchParentParentEventsRef <- newIORef []
    maybeUnsubscribeInnerERef <- newIORef <=< fix $ \subscribeAndResetOnInvalidate -> do
      weakInvalidator :: Weak Invalidator <- mkWeakPtr
        (readIORef maybeUnsubscribeInnerERef
              >>= mapM_ ((>> (do writeIORef switchParentParentEventsRef []
                                 writeIORef maybeUnsubscribeInnerERef =<< subscribeAndResetOnInvalidate))
                         . unsubscribe))
        Nothing
      fmap Just . (`subscribe` propagate)
        <=< runReaderT switchParent . Just
        $ ( weakInvalidator
          , switchParentParentEventsRef
          )
    pure $ Subscription
           (readIORef maybeUnsubscribeInnerERef
            >>= mapM_ ((>> (writeIORef switchParentParentEventsRef [] -- TODO: repeated above -- TODO: invent subscribing/unsubscribing to Behavior functions?
                        >> writeIORef maybeUnsubscribeInnerERef Nothing))
                       . unsubscribe))
           (unsafeCoerce (maybeUnsubscribeInnerERef, switchParentParentEventsRef))

  -- Hold returns a behavior which is initialized at behavior init time and changes at behavior
  -- assignment time. Whenever the behavior is sampled an invalidator action can be added which is
  -- called when the behavior changes. This is used to implement 'switch'.
  hold :: a -> Event Impl a -> Moment Impl (Behavior Impl a)
  hold v0 e = do
    invsRef :: IORef [Weak Invalidator] <- newIORef [] -- The list of invalidators that have to run whenever the result behavior changes.
    valRef <- newIORef v0
    -- Make sure not to touch 'e' eagerly, instead wait for Behavior init time.
    maybeSubscribedRef <- newIORef Nothing
    addToEnvQueue behaviorInitsRef $ writeIORef maybeSubscribedRef . Just <=< subscribe e $
      mapM_ (\a -> addToEnvQueue behaviorAssignmentsRef $ BehaviorAssignment valRef a invsRef)
    pure $ BehaviorI $ ReaderT $ \maybeInvalidatorParents -> do
      forM_ maybeInvalidatorParents $ \(invalidator, parentsRef) -> do
        modifyIORef invsRef . (:) $ invalidator
        modifyIORef parentsRef . (:) $ maybeSubscribedRef -- TODO: Reflex uses a tree data type for sharing of parents
      readIORef valRef

  now :: Moment Impl (Event Impl ())
  now = headE rootTickE

  -- Sample takes extra care to be lazy by delaying the evaluation of the sampled behavior.  The
  -- last moment by which the sample would need to be forced is the behavior's invalidation time,
  -- but here I've forced the evaluation at the next behavior init time.
  sample :: Behavior Impl a -> Moment Impl a
  sample (BehaviorI b) = do
    res <- unsafeInterleaveIO $ runReaderT b Nothing
    weakRes <- mkWeakPtr res Nothing
    addToEnvQueue behaviorInitsRef $ mapM_ evaluate =<< deRefWeak weakRes
    pure res

-- | An update to a behavior's cached value.
data BehaviorAssignment where
  BehaviorAssignment :: IORef a -> a -> IORef [Weak Invalidator] -> BehaviorAssignment


-- | Returns an event which can have multiple subscribers and a propagating/cache update procedure. The propagator
-- is not allowed to be called outside of a frame (this is unenforced)!
managedSubscribersEvent :: IO (IO ()) -> IO (Event Impl a, Maybe a -> IO (), SubscribersRef a)
managedSubscribersEvent subscribe = do
  subscribersRef <- newIORef mempty
  ctrRef <- newIORef 0
  occRef <- newIORef Nothing
  let unitializedVal = error "managedSubscribersEvent: unsubscribeRef unitialized"
  unsubscribeRef <- newIORef unitializedVal
  pure
    ( EventI $ \propagate -> do
        oldSubscribers <- readIORef subscribersRef
        when (IntMap.null oldSubscribers) $ do
          writeIORef unsubscribeRef =<< subscribe
        thisSubId <- atomicModifyIORef ctrRef (\i -> (succ i, i))
        propagateRef <- newIORef propagate
        propagateRefWeak <- mkWeakIORef propagateRef $ do
          old <- readIORef subscribersRef
          unless (IntMap.member thisSubId old) $ error "managedSubscribers unsubscribed twice"
          modifyIORef subscribersRef (IntMap.delete thisSubId)
          isEmpty <- IntMap.null <$> readIORef subscribersRef
          when isEmpty $ do
            join $ readIORef unsubscribeRef
            writeIORef unsubscribeRef unitializedVal
        modifyIORef subscribersRef . IntMap.insert thisSubId $ propagateRefWeak
        -- If occRef is already Just we have to propagate on subscribe
        -- because the subscription on e has already propagated:
        mapM_ propagate =<< readIORef occRef
        pure $ Subscription (finalize propagateRefWeak) (unsafeCoerce propagateRef)
    , \occ -> do
        writeAndScheduleClear "managedSubscribersEvent" occRef occ
        mapM_ (\x -> do
                  xm <- deRefWeak x
                  for_ xm $ \y -> do
                    prop <- readIORef y
                    prop occ)
          =<< readIORef subscribersRef
    , subscribersRef
    )

-- | Cache event occurrences.
cacheEvent :: forall a. Event Impl a -> Event Impl a
cacheEvent e = unsafePerformIO $ mdo
  ~(eCached, doPropagate, _) <- managedSubscribersEvent . fmap unsubscribe $ subscribe e doPropagate
  pure eCached

-- | For use in 'runFrame'.
newtype EventTrigger = EventTrigger { runEventTrigger :: IO () }

-- | Create a new event. Returns a "make trigger" function to which you can pass an occurrence value
-- and obtain an 'EventTrigger' for use with 'runFrame', and the new event.
newEvent :: IO (a -> EventTrigger, Event Impl a)
newEvent = do
  occRef <- newIORef Nothing -- Root event (non-)occurrence is always "known", thus Maybe a
  pure ( EventTrigger . writeAndScheduleClear "newEvent" occRef
       , mapMaybeMoment (const (readIORef occRef)) rootTickE
       )

-- | Subscribe to an event to obtain a "read occurrence" action which will contain the event
-- occurrence value when read inside the 'program' argument of 'runFrame'.
subscribeEvent :: forall a. Event Impl a -> IO (ReadTime (Maybe a), Subscription)
subscribeEvent e = do
  occRef :: IORef (Maybe (Maybe a)) <- newIORef Nothing
  unsubscribe <- subscribe e $ writeAndScheduleClear "subscribeEvent" occRef
  pure ( ReadTime $ fromMaybe (error "Occurrence read outside of runFrame?") <$> readIORef occRef
       , unsubscribe
       )

-- | For use in obtaining Event and Behavior values in 'runFrame'.
newtype ReadTime a = ReadTime { runReadTime :: IO a }
  deriving (Functor,Applicative,Monad)

-- | Return the current value of the behavior at "read time". If you want to read the next value of
-- a behavior you'll have to run 'runFrame' again, which can be done without triggering any events.
readBehavior :: Behavior Impl a -> ReadTime a
readBehavior (BehaviorI b) = ReadTime $ runReaderT b Nothing

-- | Inside the second argument you can read behaviors with 'readBehavior' and event occurrences
-- (after subscribing to an event with 'subscribeEvent').
runFrame :: [EventTrigger] -> ReadTime a -> IO a
runFrame triggers program = do
  let (Env { postTraversalQueueRef, behaviorInitsRef, behaviorAssignmentsRef }) = theEnv
  mapM_ runEventTrigger triggers
  propagateRoot
  res <- runReadTime program
  -- Lazily initialize behaviors here. Behavior initialization can queue up other behavior
  -- initialization if an untouched behavior is sampled.
  fix $ \runHoldInits -> do
    inits <- readIORef behaviorInitsRef
    unless (null inits) $ do
      writeIORef behaviorInitsRef []
      sequence_ inits
      runHoldInits
  -- Clear event occurrence caches and unsubscribe from events.
  atomicModifyIORef postTraversalQueueRef ([],) >>= sequence_
  -- Perform the updates of the behaviors' cached values.
  atomicModifyIORef behaviorAssignmentsRef ([],)
    >>= mapM_ (\(BehaviorAssignment valRef a invalidatorsRef) -> do
                  writeIORef valRef a
                  atomicModifyIORef invalidatorsRef ([],) >>= mapM_ (sequence_ <=< deRefWeak))
  flip unless (error "queues were not empty after runFrame")
    . and =<< sequence [ null <$> readIORef behaviorInitsRef
                       , null <$> readIORef postTraversalQueueRef
                       , null <$> readIORef behaviorAssignmentsRef
                       ]
  pure res

-- | Write a value to an event occurrence cache/IORef and schedule it to be cleared.
writeAndScheduleClear :: String -> IORef (Maybe a) -> a -> IO ()
writeAndScheduleClear name occRef a = do
  prev <- readIORef occRef
  when (isJust prev) $ error $ name <> ": occRef written twice---loop?"
  writeIORef occRef (Just a)
  addToEnvQueue postTraversalQueueRef $ writeIORef occRef Nothing

-- | See 'runFrame' for how these queues are processed and used.
data Env = Env
  { postTraversalQueueRef :: IORef [IO ()]
  , behaviorInitsRef :: IORef [IO ()]
  , behaviorAssignmentsRef :: IORef [BehaviorAssignment]
  }

{-# NOINLINE theEnv #-}
theEnv :: Env
theEnv = unsafePerformIO $ Env <$> newIORef [] <*> newIORef [] <*> newIORef []

addToEnvQueue :: (Env -> IORef [a]) -> a -> IO ()
addToEnvQueue selector a = modifyIORef (selector theEnv) (a:)
