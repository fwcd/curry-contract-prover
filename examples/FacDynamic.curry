-- Without precondition verification, the precondition of `fac`
-- must be checked in each recursive call:

fac :: Int -> Int
fac n | n == 0 = 1
      | n >  0 = n * fac (n - 1)

fac'pre :: Int -> Bool
fac'pre n = n >= 0

f :: Int -> Int
f x = fac x
