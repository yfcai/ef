{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

type ChurchList a = forall b. b -> (a -> b -> b) -> b

empty :: ChurchList a
empty = const

prepend :: a -> ChurchList a -> ChurchList a
prepend x ys = \ nil cons -> cons x (ys nil cons)

append :: ChurchList a -> a -> ChurchList a
append xs y = \ nil cons -> xs (cons y nil) cons

concat :: ChurchList a -> ChurchList a -> ChurchList a
concat xs ys = \nil cons -> xs (ys nil cons) cons

type Match a = forall b. b -> (a -> ChurchList a -> b) -> b

match :: ChurchList a -> Match a

tail :: ChurchList a -> ChurchList a
-- tail xs = match xs undefined (const id)
tail xs = match xs undefined (\x xs -> xs)

match = undefined

-- match xs = xs const (\ x ys nil cons -> cons x (ys empty prepend))

{-
match xs =
  xs
    const
    (\ x (ys :: Match a) ->
      ((\ nil cons -> cons x (ys empty prepend :: ChurchList a)) :: Match a))
-}

{-
match (xs :: ChurchList a) = xsSpecialized matchNil matchCons
  where
    xsSpecialized :: Match a -> (a -> Match a -> Match a) -> Match a
    xsSpecialized = xs

    matchNil :: Match a
    matchNil = const

    matchCons :: a -> Match a -> Match a
    matchCons x ys = result
      where
        result :: Match a
        result nil cons = cons x (ys empty prepend)
-}

list1 :: ChurchList Integer
list1 = prepend 1 $ prepend 2 $ prepend 3 $ prepend 4 $ empty


