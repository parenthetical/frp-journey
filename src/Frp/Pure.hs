{-# LANGUAGE TypeFamilies #-}
module Frp.Pure where

import Frp.Class
import Data.Kind (Type)
import Control.Monad.Fix
import Control.Monad
import Data.Align (align)
import Control.Monad.Trans.Maybe

data Pure (t :: Type)

instance (Ord t, Enum t) => Frp (Pure t) where
  newtype Behavior (Pure t) a = Behavior { at :: t -> a }
    deriving (Functor,Applicative,Monad,MonadFix)
  newtype Event (Pure t) a = Event { occurs :: t -> Maybe a }
  type Moment (Pure t) = (->) t
  mapMaybeMoment f = Event . runMaybeT . (MaybeT . f <=< MaybeT . occurs)
  coincidence = mapMaybeMoment occurs
  merge a b = Event $ align <$> occurs a <*> occurs b
  never = Event $ pure Nothing
  switch = Event . (occurs <=< sample)

instance (Ord t, Enum t) => MonadMoment (Pure t) ((->) t) where
  now t = Event $ guard . (t ==)
  sample = at
  hold a (Event e) from = Behavior $ \t ->
    if t <= from
    then a
    else case e (pred t) of
      Just a' -> a'
      Nothing -> sample (hold a (Event e) from) (pred t)
  liftMoment = id
