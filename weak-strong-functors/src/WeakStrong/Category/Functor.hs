{-# LANGUAGE NoImplicitPrelude #-}

module WeakStrong.Category.Functor where

class Functor f where
  fmap :: (a -> b) -> f a -> f b
