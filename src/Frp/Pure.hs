{-# LANGUAGE TypeFamilies #-}
module Frp.Pure where

import Frp.Class
import Data.Kind (Type)
import Control.Monad.Fix
import Control.Monad
import Data.Align (align)

data Pure (t :: Type)

instance (Ord t, Enum t) => Frp (Pure t) where
  newtype Behavior (Pure t) a = Behavior { sample :: t -> a }
    deriving (Functor,Applicative,Monad,MonadFix)
  newtype Event (Pure t) a = Event { occurs :: t -> Maybe a }
  type Moment (Pure t) = ((->) t)
  mapMaybeMoment f (Event e) = Event $ \t -> ($ t) . f =<< e t
  coincidence (Event e) = Event $ \t -> (($ t) . occurs) =<< e t
  merge a b = Event $ \t -> align (occurs a t) (occurs b t)
  never = Event $ pure Nothing
  switch b = Event $ \t -> occurs (Frp.Pure.sample b t) t

instance (Ord t, Enum t) => MonadMoment (Pure t) ((->) t) where
  now t = Event (guard . (t ==))
  sample = Frp.Pure.sample
  hold a (Event e) from = Behavior $ \t ->
    if t <= from
    then a
    else case e (pred t) of
      Just a' -> a'
      Nothing -> Frp.Pure.sample (hold a (Event e) from) (pred t)
