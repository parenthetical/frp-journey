{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
module Frp.Class where
import Control.Monad.Fix
import Data.Kind (Type)
import Data.These
import Data.Semigroup (Semigroup(..),First(..))
import Data.List.NonEmpty (nonEmpty, NonEmpty)
import qualified Data.Map as Map
import Data.Map (Map)
import Witherable
import Prelude hiding (filter)
import Data.These.Combinators (justThis)
import Data.Align (Semialign(..))
import Data.Functor.Misc (Const2, mapToDMap)
import Data.GADT.Compare (GCompare)
import Data.Dependent.Map (DMap)
import Control.Monad.Identity (Identity (..))
import qualified Data.Dependent.Map as DMap

class (MonadFix (Behavior t), MonadFix (Moment t)) => Frp (t :: Type) where
  data Behavior t :: Type -> Type
  data Event t :: Type -> Type
  type Moment t :: Type -> Type
  mapMaybeMoment :: (a -> Moment t (Maybe b)) -> Event t a -> Event t b
  coincidence :: Event t (Event t a) -> Event t a
  merge :: Event t a -> Event t b -> Event t (These a b)
  never :: Event t a
  switch :: Behavior t (Event t a) -> Event t a
  now :: Moment t (Event t ())
  sample :: Behavior t a -> Moment t a
  hold :: a -> Event t a -> Moment t (Behavior t a)

mapMoment :: Frp t => (a -> Moment t b) -> Event t a -> Event t b
mapMoment f = mapMaybeMoment (fmap Just . f)

instance Frp t => Functor (Event t) where
  fmap f = mapMaybeMoment (pure . Just . f)

headE :: (Frp t) => Event t a -> Moment t (Event t a)
headE e = mfix $ fmap switch . hold e . fmap (const never)

instance (Frp t, Semigroup a) => Semigroup (Event t a) where
  a <> b = these id id (<>) <$> merge a b

instance (Frp t, Semigroup a) => Monoid (Event t a) where
  mempty = never

(<@>) :: Frp t => Behavior t (a -> b) -> Event t a -> Event t b
(<@>) b = mapMoment $ \x -> do
  f <- sample b
  pure . f $ x
infixl 4 <@>

(<@?>) :: Frp t => Behavior t (a -> Maybe b) -> Event t a -> Event t b
(<@?>) b = mapMaybeMoment $ \x -> do
  f <- sample b
  pure . f $ x
infixl 4 <@?>

(<@) :: (Frp t) => Behavior t b -> Event t a -> Event t b
(<@) = tag
infixl 4 <@

tag :: Frp t => Behavior t b -> Event t a -> Event t b
tag b = mapMoment $ \_ -> sample b

accum :: (Frp t) => (a -> b -> a) -> a -> Event t b -> Moment t (Behavior t a)
accum f a e = mfix $ \x -> hold a . mapMoment (\b -> (`f` b) <$> sample x) $ e

accumE :: (Frp t) => (a -> b -> a) -> a -> Event t b -> Moment t (Event t a)
accumE f a e = mdo
  let e' = mapMoment (\q -> (`f` q) <$> sample b) e
  b <- hold a e'
  pure e'

count :: (Frp t, Num n, Enum n) => Event t a -> Moment t (Behavior t n)
count = accum (\a _ -> succ a) 0

attachWith :: Frp t => (a1 -> a2 -> b) -> Behavior t a1 -> Event t a2 -> Event t b
attachWith f b e = f <$> b <@> e

leftmost :: Frp t => [Event t a] -> Event t a
leftmost = maybe never (fmap getFirst . sconcat . fmap (fmap First)) . nonEmpty

mergeMap :: (Frp t, Ord k) => Map k (Event t a) -> Event t (Map k a)
mergeMap = mconcat . fmap (\(t,e) -> Map.singleton t <$> e) . Map.toList

switchHoldPromptly :: (Frp t) => Event t a -> Event t (Event t a) -> Moment t (Event t a)
switchHoldPromptly ea0 eea = do
  bea <- hold ea0 eea
  let eLag = switch bea
      eCoincidences = coincidence eea
  return $ leftmost [eCoincidences, eLag]

instance Frp t => Filterable (Event t) where
  mapMaybe f = mapMaybeMoment (pure . f)

difference :: Frp t => Event t b1 -> Event t b2 -> Event t b1
difference a b = mapMaybe justThis $ merge a b


data Dynamic t a = Dynamic { updated :: Event t a, current :: Behavior t a }

unsafeBuildDynamic :: Event t a -> Behavior t a -> Dynamic t a
unsafeBuildDynamic = Dynamic

instance Frp t => Semialign (Event t) where
  align = merge

zipDynWith :: Frp t => (a -> b -> c) -> Dynamic t a -> Dynamic t b -> Dynamic t c
zipDynWith f da db =
  let eab = align (updated da) (updated db)
      ec = flip mapMoment eab $ \o -> do
        (a, b) <- case o of
          This a -> do
            b <- sample $ current db
            return (a, b)
          That b -> do
            a <- sample $ current da
            return (a, b)
          These a b -> return (a, b)
        return $ f a b
  in unsafeBuildDynamic ec (f <$> current da <*> current db)


instance (Frp t) => Functor (Dynamic t) where
  fmap f (Dynamic u c) = Dynamic (fmap f u) (fmap f c)

instance (Frp t) => Applicative (Dynamic t) where
  pure = Dynamic never . pure
  liftA2 = zipDynWith
  a <*> b = zipDynWith ($) a b
  a *> b = unsafeBuildDynamic (leftmost [updated b, tag (current b) $ updated a]) (current b)
  (<*) = flip (*>) -- There are no effects, so order doesn't matter

instance (Frp t) => Monad (Dynamic t) where
  x >>= f =
    let d = fmap f x
    in unsafeBuildDynamic
       (leftmost
         [ coincidence $ updated <$> updated d -- both
         , mapMoment (sample . current) $ updated d -- outer
         , switch $ updated <$> current d -- eInner
         ])
       (current =<< current d)
  (>>) = (*>)


foldDyn :: (Frp t) => (a -> b -> b) -> b -> Event t a -> Moment t (Dynamic t b)
foldDyn = accumDyn . flip

accumDyn :: (Frp t1) => (t2 -> t3 -> t2) -> t2 -> Event t1 t3 -> Moment t1 (Dynamic t1 t2)
accumDyn f = accumMaybeDyn $ \v o -> Just $ f v o

accumMaybeDyn :: (Frp t) => (t2 -> t3 -> Maybe t2) -> t2 -> Event t t3 -> Moment t (Dynamic t t2)
accumMaybeDyn f = accumMaybeMDyn $ \v o -> return $ f v o

holdDyn :: Frp t => a -> Event t a -> Moment t (Dynamic t a)
holdDyn v0 e = Dynamic e <$> hold v0 e

accumMaybeMDyn
  :: (Frp t)
  => (a -> b -> Moment t (Maybe a))
  -> a
  -> Event t b
  -> Moment t (Dynamic t a)
accumMaybeMDyn f z e = do
  rec let e' = flip mapMaybeMoment e $ \o -> do
            v <- sample $ current d'
            f v o
      d' <- holdDyn z e'
  return d'

distributeListOverDyn :: Frp t => [Dynamic t a] -> Dynamic t [a]
distributeListOverDyn = sequence

buildDynamic :: (Frp t) => Moment t a -> Event t a -> Moment t (Dynamic t a)
buildDynamic v0 e = do
  i <- v0
  Dynamic e <$> hold i e

fan :: forall t k. (Frp t, GCompare k)
    => Event t (DMap k Identity) -> EventSelector t k
fan e = EventSelector $ \k -> mapMaybe (fmap runIdentity . DMap.lookup k) e

mergeList :: Frp t => [Event t a] -> Event t (NonEmpty a)
mergeList = mapMaybe nonEmpty . mconcat . fmap (fmap (:[]))

fanMap :: (Frp t, Ord k) => Event t (Map k a) -> EventSelector t (Const2 k a)
fanMap = fan . fmap mapToDMap

newtype EventSelector t k = EventSelector { select :: forall a. k a -> Event t a }

