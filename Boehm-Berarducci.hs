{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

-- Böhm-Berarducci encoding of algebraic data types
-- This is how you write `tail` in terms of `fold`.

-- Böhm-Beraducci encoded list

-- first, start with the type of "fold" for that data.
type List  a = forall b. b -> (a -> b -> b) -> b
type Final a = forall b. b -> (a -> List a -> b) -> b

toFinal :: forall a. List a ->  forall b. Final b
toFinal xs = xs dnil dcons where
  dnil = undefined
  dcons = undefined
