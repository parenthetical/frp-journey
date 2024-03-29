{-# LANGUAGE TypeFamilies #-}
{-|
Description: A pure (non-IO) implementation of the Frp interface.

In this pure implementation of 'Frp.Class.Frp', events, Behaviors, and Moment are implemented as
functions of time.  The implementation avoids referencing time whenever possible to make it clear
which functions depend only on some "current time" or the past as well.
-}
module Frp.Pure where

import Frp.Class
import Data.Kind (Type)
import Control.Monad.Fix
import Control.Monad
import Data.Align (align)
import Control.Monad.Trans.Maybe
import Data.Maybe ( fromMaybe )

data Pure (t :: Type)

instance (Ord t, Enum t) => Frp (Pure t) where
  newtype Behavior (Pure t) a = BehaviorP { at :: t -> a }
    deriving (Functor,Applicative,Monad,MonadFix)
  newtype Event (Pure t) a = EventP { occurs :: t -> Maybe a }
  type Moment (Pure t) = (->) t
  mapMaybeMoment f = EventP . runMaybeT . (MaybeT . f <=< MaybeT . occurs)
  coincidence = mapMaybeMoment occurs
  merge a b = EventP $ align <$> occurs a <*> occurs b
  never = EventP $ pure Nothing
  switch = EventP . (occurs <=< sample)
  now = fmap (EventP . fmap guard) (==)
  sample = at
  hold a e from = BehaviorP $ \t ->
    if t <= from
    then a
    else fromMaybe (sample (hold a e from) (pred t)) $ occurs e (pred t)
