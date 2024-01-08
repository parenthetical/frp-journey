{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
module Frp.Test where

import Frp.Impl
import Frp.Class
import Data.Kind (Type)
import Control.Monad.State
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import System.Mem (performGC)
import Witherable (catMaybes)
import Frp.Pure
import Data.Bifunctor (first)
import qualified Data.IntSet as IntSet
import Control.Monad.Fix (MonadFix)
import Data.Maybe (fromMaybe)
import Control.Monad (forM, when, join)
import qualified Data.Map as Map
import System.Exit
import Data.Char (toUpper)
import Data.Functor (void)
import Data.IntSet (IntSet)

newtype PlanImpl a where
  PlanImpl :: (StateT Schedule (Moment Impl) a) -> PlanImpl a
  deriving (Functor,Applicative,Monad,MonadFix)

type Schedule = IntMap [EventTrigger]

newtype PlanPure a = PlanPure (StateT IntSet (Moment (Pure Int)) a)
  deriving (Functor,Applicative,Monad,MonadFix)

instance () => TestPlan Impl PlanImpl where
  plan occurrences = PlanImpl $ do
    (makeTrigger, e) <- liftIO newEvent
    modify . IntMap.unionWith mappend . IntMap.fromList
      . fmap (\(t,a) -> (fromIntegral t, [makeTrigger a]))
      $ occurrences
    pure e
  liftPlan = PlanImpl . lift


mapToPureEvent :: IntMap a -> Event (Pure Int) a
mapToPureEvent m = EventP $ flip IntMap.lookup m

instance TestPlan (Pure Int) PlanPure where
  plan occurrences = do
    let m = IntMap.fromList (first fromIntegral <$> occurrences)
    PlanPure . modify $ IntSet.union (IntMap.keysSet m)
    pure $ mapToPureEvent m
  liftPlan = PlanPure . lift

runPlanImplE :: PlanImpl (Event Impl b) -> IO (IntMap b)
runPlanImplE (PlanImpl x) = do
  (e,s) <- runStateT x mempty
  readOcc <- subscribeEvent e
  catMaybes
    <$> traverse (\occs -> do
                             performGC
                             runFrame occs readOcc)
        (makeDense s)
-- TODO: commonalities between runPlanImpl*
runPlanImplB :: PlanImpl (Behavior Impl b) -> IO (IntMap b)
runPlanImplB (PlanImpl x) = do
  (b,s) <- runStateT x mempty
  traverse (\occs -> do
               performGC
               runFrame occs (readBehavior b))
    (makeDense s)

runPure :: PlanPure a -> (a, IntSet)
runPure (PlanPure p) = runStateT p mempty 0

relevantTimes :: IntSet -> IntSet
relevantTimes occs = IntSet.fromList [0..l + 1]
  where l = maybe 0 fst (IntSet.maxView occs)

testBehavior :: (Behavior (Pure Int) a, IntSet) -> IntMap a
testBehavior (b, occs) = IntMap.fromSet (sample b) (relevantTimes occs)

testEvent :: (Event (Pure Int) a, IntSet) -> IntMap a
testEvent (EventP readEvent, occs) = catMaybes $ IntMap.fromSet readEvent (relevantTimes occs)


makeDense :: IntMap [a] -> IntMap [a]
makeDense s = fromMaybe (emptyRange 0) $ do
  (end, _) <- fst <$> IntMap.maxViewWithKey s
  return $ IntMap.union s (emptyRange end)
    where
      emptyRange end = IntMap.fromList (map (, []) [0..end + 1])


class (Frp t, Monad m, MonadFix m) => TestPlan (t :: Type) m | m -> t where
  plan :: [(Word, a)] -> m (Event t a)
  liftPlan :: Moment t a -> m a

planList :: TestPlan t m => [a] -> m (Event t a)
planList xs = plan $ zip [1..] xs

type TestE a = forall t m. TestPlan t m => m (Event t a)
type TestB a = forall t m. TestPlan t m => m (Behavior t a)

data TestCase  where
  TestE  :: (Show a, Eq a) => TestE a -> TestCase
  TestB  :: (Show a, Eq a) => TestB a -> TestCase

-- Helpers to declare test cases
testE :: (Eq a, Show a) => String -> TestE a -> (String, TestCase)
testE name test = (name, TestE test)

testB :: (Eq a, Show a) => String -> TestB a -> (String, TestCase)
testB name test = (name, TestB test)


testAgreement :: TestCase -> IO Bool
testAgreement = \case
  TestE p -> do
    impl <- runPlanImplE p
    let results = [("impl", impl)]
    compareResult results (testEvent $ runPure p)
  TestB p -> do
    impl <- runPlanImplB p
    let results = [("impl", impl)]
    compareResult results (testBehavior $ runPure p)

compareResult :: (Show a, Eq a) => [(String, IntMap a)] -> IntMap a -> IO Bool
compareResult results expected = fmap and $ forM results $ \(name, r) -> do
  when (r /= expected) $ do
    putStrLn ("Got: " ++ show (name, r))
    putStrLn ("Expected: " ++ show expected)
  pure (r == expected)

runTests :: [(String, TestCase)] -> IO ()
runTests cases = do
   results <- forM cases $ \(name, test) -> do
     putStrLn $ "Test: " <> name
     testAgreement test
   exitWith $ if and results
              then ExitSuccess
              else ExitFailure 1

testCases :: [(String, TestCase)]
testCases =
  [ testB "hold-0"  $ liftPlan . hold "0" =<< events1
  , testB "count" $ do
      b <- liftPlan . count =<< events2
      pure $ (+ (0::Int)) <$> b
  , testB "behavior-0" $ liftA2 (<>) <$> behavior1 <*> behavior2
  , testB "behavior-1" $ do
      es <- planList ["a", "b", "c"]
      e <- plan [(0, ())]
      b <- liftPlan $ hold (pure "") $
        mapMoment (const $ hold "z" es) e
      pure (join b)
  , testE "id" events2
  , testE "fmap-simple" $ fmap (<> "x") <$> events2
  , testE "tag-1" $ (<@) <$> behavior1 <*> events2
  , testE "tag-2" $ (<@) <$> (fmap (fmap toUpper) <$> behavior1) <*> events2
  , testE "attach-1" $ do
      b1 <- behavior1
      attachWith (++) (fmap toUpper <$> b1) <$> events2
  , testE "leftmost" $ liftA2 leftmost2 events1 events2

  , testE "appendEvents-1" $ liftA2 mappend events1 events2

  , testE "appendEvents-2" $ liftA2 mappend events3 events2

  , testE "merge-1" $ do
      e <- events1
      pure $ leftmost ["x" <$ e, "y" <$ e]

  , testE "merge-2" $ do
      e <- events1
      let m = mergeMap $ Map.fromList [(1::Int, "y" <$ e), (2, "z" <$ e)]
      let ee = flip mapMoment e $ const $ pure m
      pure $ coincidence ee

  , testE "headE-0" $ liftPlan . headE =<< events1
  , testE "headE-1" $ do
      e <- events1
      liftPlan $ headE $ leftmost [e, e]

  , testE "headE-2" $ do
      e <- events1
      liftPlan $ do b <- hold never (e <$ e)
                    headE $ switch b

  , testE "switch-1" $ do
      e <- events1
      b <- liftPlan $ hold never (e <$ e)
      pure $ switch b

  , testE "switch-2" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $ switch <$> hold (leftmost ["x" <$ e, "y" <$ e, "z" <$ e]) (e <$ e)

  , testE "switch-3" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $ switch <$> hold (leftmost ["x" <$ e, "y" <$ e, "z" <$ e]) never

  , testE "switch-4" $ do
      e <- events1
      liftPlan $ switch <$> hold (deep e) (e <$ e)

  , testE "switch-5" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $
        pure $ leftmost ["x" <$ e, "y" <$ e, "z" <$ e]

  , testE "switch-6" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $ switch <$> hold ("x" <$ e) (e <$ e)

  , testE "switchHoldPromptly-1" $ do
      e <- events1
      let e' = e <$ e
      liftPlan $ switchHoldPromptly never $ e <$ e'

  , testE "switchHoldPromptly-2" $ do
      e <- events1
      liftPlan $ switchHoldPromptly never $ deep (e <$ e)

  , testE "switchHoldPromptly-3" $ do
      e <- events1
      liftPlan $ switchHoldPromptly never (e <$ deep e)

  , testE "switchHoldPromptly-4" $ do
      e <- events1
      liftPlan $ switchHoldPromptly never (deep e <$ e)

  , testE "switch-6" $ do
      e <- events1
      liftPlan $ switch <$> hold never (deep e <$ e)

  , testE "switchHoldPromptly-5" $ do
    e <- events1
    liftPlan $ switchHoldPromptly never $ flip mapMaybeMoment e $
      const (Just <$> headE e)

  , testE "switchHoldPromptly-6" $ do
      e <- events1
      liftPlan $ switchHoldPromptly never $ flip mapMoment e $
        const (switchHoldPromptly e never)

  , testE "coincidence-1" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $
        const $ pure e

  , testE "coincidence-2" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $
        const $ pure (deep e)

  , testE "coincidence-3" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $
        const $ pure (coincidence (e <$ e))

  , testE "coincidence-4" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $
        const (headE e)

  , testE "coincidence-5" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $ do
        let e' = deep e
        pure (coincidence (e' <$ e'))

  , testE "coincidence-6" $ do
      e <- events1
      pure $ coincidence $ flip mapMoment e $ const $ do
        let e' = coincidence (e <$ e)
        pure $ deep e'

  , testE "coincidence-7" $ do
      e <- events1
      pure $ coincidence (deep e <$ e)

  , testB "holdWhileFiring" $ do
      e <- events1
      liftPlan $  do
        eo <- headE e
        bb <- hold (pure "x") $ mapMoment (const $ hold "a" eo) eo
        pure $ join bb

  , testE "joinDyn" $ do
      e <- events1
      liftPlan $ do
        bb <- hold "b" e
        bd <- hold never . fmap (const e) =<< headE e

        eOuter <- mapMoment sample . fmap (const bb) <$> headE e
        let eInner = switch bd
        pure $ leftmost [eOuter, eInner]

  , testB "holdSampleStrictness"  $ do
      e1 <- events1
      liftPlan $ do
        rec
          a <- sample b
          b' <- hold a e1
          b <- hold "0" e1
          _ <- sample b'
        pure b'

  , testE "difference" $ do
      e1 <- events1
      e2 <- events2
      pure $ e1 `difference ` e2

  , testE "lazy-hold" $ do
      let lazyHold :: forall t. (Frp t) => Moment t (Event t ())
          lazyHold = do
            rec !b <- hold never e
                let e = never <$ switch b
            pure $ void e
      liftPlan lazyHold
  , testE "now-1" $ do
      e1 <- events1
      liftPlan $ switchHoldPromptly never . mapMoment (\a -> fmap (a <$) now) $ e1
  , testE "now-2" $ do
      e1 <- events1
      let e = mapMoment (\a -> if a == "a" then now else pure never) e1
      x <- liftPlan $ accumE (<>) never e
      pure . coincidence $ x
  , testE "now-3" $ liftPlan now
  , testE "now-4" $ do
      coincidence . mapMoment (\a -> if a == "a" then now else pure never) <$> events1

  ]  where
    events1, events2, events3 ::  TestPlan t m => m (Event t String)
    events1 = plan [(1, "a"), (2, "b"), (5, "c"), (7, "d"), (8, "e")]
    events2 = plan [(1, "e"), (3, "d"), (4, "c"), (6, "b"), (7, "a")]
    events3 = liftA2 mappend events1 events2

    behavior1, behavior2 :: forall t m. TestPlan t m => m (Behavior t String)
    behavior1 =  liftPlan . hold "1" =<< events1
    behavior2 =  liftPlan . hold "2" =<< events2

    deep e = leftmost [e, e]
    leftmost2 e1 e2 = leftmost [e1, e2]
