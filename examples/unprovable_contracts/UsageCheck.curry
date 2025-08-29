f'pre :: Int -> Bool
f'pre = const True

f'post :: Int -> Int -> Bool
f'post = const . const $ True

g'post :: Int -> Int -> Bool
g'post = const . const $ True

f :: Int -> Int
f = (* 2)
