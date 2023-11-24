{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DefaultSignatures #-}
module Frp.Class where
import Control.Monad.Fix
import Data.Kind (Type)
import Data.These
import Data.Bool (bool)
import Control.Monad.Trans
import Data.Semigroup (Semigroup(..),First(..))
import Data.List.NonEmpty (nonEmpty)
import qualified Data.Map as Map
import Data.Map (Map)
import Witherable
import Prelude hiding (filter)
import Data.These.Combinators (justThis)

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

class MonadMoment t m where
  now :: m (Event t ())
  default now :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => m (Event t ())
  now = lift now
  sample :: Behavior t a -> m a
  default sample :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => Behavior t a -> m a
  sample = lift . sample
  hold :: a -> Event t a -> m (Behavior t a)
  default hold :: (m ~ f m', MonadTrans f, Monad m', MonadMoment t m') => a -> Event t a -> m (Behavior t a)
  hold a = lift . hold a
  
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
