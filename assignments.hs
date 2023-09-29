module Assignments where
import Data.Char
import Test.QuickCheck
import Data.List
f :: Num a => a -> a   -- assignment 4.1
f x = 2 * ( x ^ 2 ) + 3 * x - 5

circ :: Double -> Double   -- assignment 4.2
circ r = 2 * pi * r

area :: Double -> Double   -- assignment 4.2
area r = pi * r ^ 2

discr :: Num a => a -> a -> a -> a   -- assignment 4.3
discr a b c = b^2 - 4 * a * c
root1 :: (Ord a, Floating a) => a -> a -> a -> a
root1 a b c | discr a b c >= 0 = (-b + sqrt(discr a b c))/(2 * a)
 | otherwise = error "discriminant negative"

root2 :: (Ord a, Floating a) => a -> a -> a -> a   -- assignment 4.3
root2 a b c | discr a b c >= 0 = (-b - sqrt(discr a b c))/(2 * a)
 | otherwise = error "discriminant negative"

extrX :: Fractional a => a -> a -> p -> a   -- assignment 4.4
extrX a b c = (-b)/(2*a)
extrY :: Fractional a => a -> a -> a -> a
extrY a b c = a*x^2 + b*x + c where x = extrX a b c

isEnUpper :: Char-> Bool   -- assignment 4.5
isEnUpper x = (x>='A') && (x<='Z')

isEnLower :: Char-> Bool
isEnLower x = (x>='a') && (x<='z')

total1 :: Int -> Int   --assignment 4.6
total1 0 = 0
total1 n = total1 (n-1) + n

total2 :: Int -> Int
total2 n = ( n * ( n + 1 ) ) `div` 2

prop_total :: Int -> Property
prop_total n = (n >= 0) ==> total1 n == total2 n

total1' :: Int -> Int   -- assignment 4.6
total1' 0 = 0
total1' n = total1 (n-1) + n

total2' :: Int -> Int
total2' n = ( n * n ) `div` 2

prop_total' :: Int -> Property
prop_total' n = (n >= 0) ==> total1 n == total2 n 

interest :: (Eq t1, Num t1, Fractional t2) => t2 -> t2 -> t1 -> t2   --assignment 4.7
interest a p 0 = 0
interest a p 1 = a + ((a*p)/100)
interest a p y = interest a p (y-1) + (interest a p (y-1)*p/100)

mylength :: Num a1 => [a2] -> a1   --assignment 4.8 a
mylength [] = 0
mylength (x:xs) = 1 + mylength xs

prop_mylength :: [a2] -> Bool
prop_mylength xs = length xs == mylength xs


mysum :: [Int] -> Int   --assignment 4.8 b
mysum [] = 0
mysum (x:xs) = x + mysum xs

prop_mysum :: [Int] -> Bool
prop_mysum xs = mysum xs == sum xs


myreverse :: [a] -> [a]   -- assignment 4.8 c
myreverse [] = []
myreverse (x:xs) = myreverse xs ++ [x]

prop_myreverse :: Eq a => [a] -> Bool
prop_myreverse xs = myreverse xs == reverse xs


mytake :: (Eq t, Num t) => t -> [a] -> [a]   --assignment 4.8 d
mytake 0 (x:xs) = []
mytake n [] = []
mytake n (x:xs) = x : mytake (n-1) xs

prop_mytake :: Eq a => Int -> [a] -> Property
prop_mytake n xs = n >= 0 ==> mytake n xs == take n xs


myelem :: Eq t => t -> [t] -> Bool   -- assignment 4.8 e
myelem n [] = False
myelem n (x:xs) | n == x = True
 | otherwise = myelem n xs

prop_myelem :: Eq a => a -> [a] -> Bool
prop_myelem x ys = myelem x ys == elem x ys


myconcat :: [[a]] -> [a]   -- assignment 4.8 f
myconcat [] = []
myconcat ((x:xs):ys) = x : myconcat ys

mymaximum :: Ord a => [a] -> a   -- assignment 4.8 g
mymaximum [] = error "empty list"
mymaximum [c] = c
mymaximum (c:b:rest) | c >= b = mymaximum(c:rest)
 | otherwise = mymaximum(b:rest)

prop_mymaximum :: Ord a => [a] -> Property
prop_mymaximum xs = not (null xs) ==> mymaximum xs == maximum xs

myzip :: [a] -> [b] -> [(a, b)]   -- assignment 4.8 h
myzip [] [] = []
myzip [] (x:xs) = []
myzip (x:xs) [] = []
myzip (x:xs) (y:ys) = (x,y) : myzip xs ys


r :: (Eq t1, Num t1, Num t2) => t2 -> t2 -> t1 -> t2   -- assignment 4.9 a
r a d 0 = a - d
r a d i = a + d + r 0 d (i-1)

total' :: (Ord t1, Num a, Num t1) => a -> a -> t1 -> t1 -> a   -- assignment 4.9 b
total' a d i j | i <= j = total' a d (i+1) j + r a d i
 | otherwise = 0

allEqual :: Eq a => [a] -> Bool   -- assignment 4.10 a
allEqual [] = True
allEqual [c] = True
allEqual (c:b:rest) | c == b = allEqual(c:rest)
 | otherwise = False 

dif :: Num a => [a] -> [a]   -- assignment 4.10 b
dif [] = []
dif [f] = []
dif (f:g:xs) = (g-f) : dif(g:xs)
isAs :: (Eq a, Num a) => [a] -> Bool
isAs (x:xs) = allEqual(dif(x:xs))


palin :: Eq a => [a] -> Bool   -- assignment 4.11
palin xs = xs == reverse xs


pat :: (Num a1, Eq a2) => [a2] -> [a2] -> a1   -- assignment 4.12
pat [] pattern = 0
pat n [] = 0
pat n pattern | take (length pattern) n == pattern = 1 + pat (tail n) pattern
 | otherwise = pat (tail n) pattern

dotprod :: Num a => [a] -> [a] -> a   -- assignment 4.13
dotprod [] (y:ys) = 0
dotprod (x:xs) [] = 0
dotprod [x][y] = x * y
dotprod (x:xs) (y:ys) = x*y + dotprod xs ys

pyth :: (Num c, Eq c, Enum c) => c -> [(c, c, c)]   -- assignment 4.14
pyth n = [ (a,b,c) | c <- [1..n], b <- [1..c], a <- [1..b], a^2 + b^2 == c^2]

incr :: Ord a => [a] -> Bool   -- assignment 4.15
incr [] = True
incr [f] = True
incr (f:g:xs) | f <= g = incr (g:xs)
 | otherwise = False


-- sign off assignments 4.17, 4.18, 4.19 and 4.22 (Set 3)
dividers :: Integral a => a -> [a]   -- assignment 4.17
dividers n = [ a | a <- [1..n], n `mod` a == 0]

primeDividers :: Integral a => a -> [a]   -- assignment 4.18
primeDividers n = [a | a <- [2..n-1], n `mod` a == 0]
isPrime :: Integral a => a -> Bool
isPrime n | length (primeDividers n) == 0 = True
 | otherwise = False

-- [(x, y) | x <- [1..100], y <- [1..100], x + y == 100, isPrime x, isPrime y] -- assignment 1.19

maketups :: [a] -> [(a, Int)]
maketups xs = (xs) `zip` [0..length(xs)]

alli :: Eq a => [a] -> a -> [Int]
alli xs n = [ snd as | as <- maketups xs, fst as == n] 

ins x [] = [x]
ins x (y:ys) | x <= y = x:y:ys
 |otherwise = y : ins x ys

isort [] =[]
isort (x:xs) = ins x (isort xs) 

prop_isort xs = isort xs == sort xs

merge [] (y:ys) = y:ys
merge (x:xs) [] = x:xs
merge (x:xs) (y:ys) | x <= y = x:merge xs (y:ys)
 |otherwise = y:merge(x:xs) ys


msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs = msort(take (length xs `div` 2) xs) `merge` msort(drop (length xs `div` 2) xs)

prop_msort xs = msort xs == sort xs

itn :: (Eq t1, Num t1) => (t2 -> t2) -> t2 -> t1 -> t2
itn f a 1 = f a
itn f a n = f (itn f a (n-1))


ins' r x [] = [x]
ins' r x (y:ys) | r x y = x:y:ys
 |otherwise = y : ins' r x ys

hoSort r [] = []
hoSort r (x:xs) = ins' r x (hoSort r xs)

prop_hoSort r xs = hoSort (<) xs == sort xs

dice = [(a,b) | a<-[1..6], b <- [1..6]]
diceT n = [(a,b) | a <- [1..6], b <- [1..6], a == n || b == n]

diceTh m = [(a,b)| a <- [1..6], b <- [1..6], a + b ==m]

diceThr = hoSort (<) [(a+b) | a <- [1..6], b <- [1..6] ]
