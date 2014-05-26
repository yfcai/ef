data Mu a = Roll { unroll :: Mu a -> a }

y :: (a -> a) -> a
y = \f -> (\x -> f (unroll x x)) (Roll (\x -> f (unroll x x)))

factorial :: Integer -> Integer
factorial = y (\f n -> if n == 0 then 1 else n * f (n - 1))

main = do
  putStr "    factorial of  "
  n <- readLn
  putStr "    is "
  putStrLn $ show $ factorial n


{- variants:
main = factorial 5
main = omega
-}
