{-# LANGUAGE NoImplicitPrelude #-}

module WeakStrong.Data.Maybe where

import WeakStrong.Category.Functor

data Maybe a = Nothing | Just a

instance Functor Maybe where
  fmap _ Nothing  = Nothing
  fmap f (Just x) = Just (f x)
