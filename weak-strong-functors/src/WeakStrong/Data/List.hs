{-# LANGUAGE NoImplicitPrelude #-}

module WeakStrong.Data.List where

import WeakStrong.Category.Functor

instance Functor [] where
  fmap _ []     = []
  fmap f (x:xs) = f x : fmap f xs
