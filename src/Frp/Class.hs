{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
module Frp.Class where
import Control.Monad.Fix
import Data.Kind (Type)
import Data.These
import Data.Bool (bool)
import Control.Monad.Trans
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

class
  ( MonadFix (Behavior t),
    MonadFix (Moment t),
    MonadMoment t (Moment t)
  ) =>
  Frp (t :: Type)
  where
  data Behavior t :: Type -> Type
  data Event t :: Type -> Type
  type Moment t :: Type -> Type
  mapMaybeMoment :: (a -> Moment t (Maybe b)) -> Event t a -> Event t b
  coincidence :: Event t (Event t a) -> Event t a
  merge :: Event t a -> Event t b -> Event t (These a b)
  never :: Event t a
  switch :: Behavior t (Event t a) -> Event t a

class MonadMoment t m | m -> t where
  now :: m (Event t ())
  default now :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => m (Event t ())
  now = lift now
  sample :: Behavior t a -> m a
  default sample :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => Behavior t a -> m a
  sample = lift . sample
  hold :: a -> Event t a -> m (Behavior t a)
  default hold :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => a -> Event t a -> m (Behavior t a)
  hold a = lift . hold a
  liftMoment :: Moment t a -> m a
  default liftMoment :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => Moment t a -> m a
  liftMoment = lift . liftMoment

mapMoment :: Frp t => (a -> Moment t b) -> Event t a -> Event t b
mapMoment f = mapMaybeMoment (fmap Just . f)

filterE :: Frp t => (a -> Bool) -> Event t a -> Event t a
filterE f = mapMaybeMoment (\a -> pure $ bool Nothing (Just a) (f a))

instance Frp t => Functor (Event t) where
  fmap f = mapMaybeMoment (pure . Just . f)

headE :: (Frp t, MonadMoment t m, Functor m, MonadFix m) => Event t a -> m (Event t a)
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

accum :: (Frp t, MonadFix m, MonadMoment t m) => (a -> b -> a) -> a -> Event t b -> m (Behavior t a)
accum f a e = mfix $ \x -> hold a . mapMoment (\b -> (`f` b) <$> sample x) $ e

accumE :: (Frp t, MonadFix m, MonadMoment t m) => (a -> b -> a) -> a -> Event t b -> m (Event t a)
accumE f a e = mdo
  let e' = mapMoment (\q -> (`f` q) <$> sample b) e
  b <- hold a e'
  pure e'

count :: (Frp t, MonadFix m, MonadMoment t m, Num n, Enum n) => Event t a -> m (Behavior t n)
count = accum (\a _ -> succ a) 0

attachWith :: Frp t => (a1 -> a2 -> b) -> Behavior t a1 -> Event t a2 -> Event t b
attachWith f b e = f <$> b <@> e

leftmost :: Frp t => [Event t a] -> Event t a
leftmost = maybe never (fmap getFirst . sconcat . fmap (fmap First)) . nonEmpty

mergeMap :: (Frp t, Ord k) => Map k (Event t a) -> Event t (Map k a)
mergeMap = mconcat . fmap (\(t,e) -> Map.singleton t <$> e) . Map.toList

switchHoldPromptly :: (Frp t, Monad m, MonadMoment t m) => Event t a -> Event t (Event t a) -> m (Event t a)
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


foldDyn :: (Frp t, MonadFix m, MonadMoment t m) => (a -> b -> b) -> b -> Event t a -> m (Dynamic t b)
foldDyn = accumDyn . flip

accumDyn :: (Frp t1, MonadFix m, MonadMoment t1 m) => (t2 -> t3 -> t2) -> t2 -> Event t1 t3 -> m (Dynamic t1 t2)
accumDyn f = accumMaybeDyn $ \v o -> Just $ f v o

accumMDyn :: (Frp t1, MonadFix m, MonadMoment t1 m) => (t2 -> t3 -> Moment t1 t2) -> t2 -> Event t1 t3 -> m (Dynamic t1 t2)
accumMDyn f = accumMaybeMDyn $ \v o -> Just <$> f v o

accumMaybeDyn :: (Frp t1, MonadFix m, MonadMoment t1 m) => (t2 -> t3 -> Maybe t2) -> t2 -> Event t1 t3 -> m (Dynamic t1 t2)
accumMaybeDyn f = accumMaybeMDyn $ \v o -> return $ f v o

holdDyn :: (Functor m, MonadMoment t m) => a -> Event t a -> m (Dynamic t a)
holdDyn v0 e = Dynamic e <$> hold v0 e

accumMaybeMDyn
  :: (Frp t, MonadFix m, MonadMoment t m)
  => (a -> b -> Moment t (Maybe a))
  -> a
  -> Event t b
  -> m (Dynamic t a)
accumMaybeMDyn f z e = do
  rec let e' = flip mapMaybeMoment e $ \o -> do
            v <- sample $ current d'
            f v o
      d' <- holdDyn z e'
  return d'

distributeListOverDyn :: Frp t => [Dynamic t a] -> Dynamic t [a]
distributeListOverDyn = sequence

buildDynamic :: (MonadMoment t m, Frp t, Monad m) => Moment t a -> Event t a -> m (Dynamic t a)
buildDynamic v0 e = do
  i <- liftMoment v0
  Dynamic e <$> hold i e

fan :: forall t k. (Frp t, GCompare k)
    => Event t (DMap k Identity) -> EventSelector t k
fan e = EventSelector $ \k -> mapMaybe (fmap runIdentity . DMap.lookup k) e

mergeList :: Frp t => [Event t a] -> Event t (NonEmpty a)
mergeList = mapMaybe nonEmpty . mconcat . fmap (fmap (:[]))

fanMap :: (Frp t, Ord k) => Event t (Map k a) -> EventSelector t (Const2 k a)
fanMap = fan . fmap mapToDMap

-- | An 'EventSelector' allows you to efficiently 'select' an 'Event' based on a
-- key.  This is much more efficient than filtering for each key with
-- 'mapMaybe'.
newtype EventSelector t k = EventSelector
  { -- | Retrieve the 'Event' for the given key.  The type of the 'Event' is
    -- determined by the type of the key, so this can be used to fan-out
    -- 'Event's whose sub-'Event's have different types.
    --
    -- Using 'EventSelector's and the 'fan' primitive is far more efficient than
    -- (but equivalent to) using 'mapMaybe' to select only the relevant
    -- occurrences of an 'Event'.
    select :: forall a. k a -> Event t a
  }

newtype EventSelectorG t k v = EventSelectorG
  { -- | Retrieve the 'Event' for the given key.  The type of the 'Event' is
    -- determined by the type of the key, so this can be used to fan-out
    -- 'Event's whose sub-'Event's have different types.
    --
    -- Using 'EventSelector's and the 'fan' primitive is far more efficient than
    -- (but equivalent to) using 'mapMaybe' to select only the relevant
    -- occurrences of an 'Event'.
    selectG :: forall a. k a -> Event t (v a)
  }

-- | Efficiently select an 'Event' keyed on 'Int'. This is more efficient than manually
-- filtering by key.
newtype EventSelectorInt t a = EventSelectorInt { selectInt :: Int -> Event t a }
