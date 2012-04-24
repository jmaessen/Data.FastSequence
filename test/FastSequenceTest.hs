{-# LANGUAGE BangPatterns #-}

-- | Tests for Data.FastSequence.  We test functions by comparing them to their list
-- equivalents.

module Main(main) where

import Prelude hiding ( null, reverse, length, head, tail, init, last, take, drop, splitAt,
                        replicate, scanl, scanl1, scanr, scanr1 )
import qualified Prelude as P
import qualified Data.List as L
import Control.Monad.Writer.Strict(runWriter, tell)
import Control.Applicative(WrappedMonad(WrapMonad), unwrapMonad)
import Data.FastSequence
import Data.Monoid(Sum(Sum))
import Test.Framework(Test,defaultMain,testGroup)
import Test.Framework.Providers.QuickCheck2(testProperty)
import Test.QuickCheck hiding ((><))

bigArgs = stdArgs{ maxSize = 1000, maxSuccess = 1000, maxDiscard = 1000 }

qC prop = quickCheckWith bigArgs prop

------------------------------------------------------------
-- * Properties

------------------------------------------------------------
-- ** Empty and to/from list

prop_empty :: Bool
prop_empty = null empty && P.null (toList empty)

prop_fromList_toList :: [Int] -> Bool
prop_fromList_toList xs = toList (check $ fromList xs) == xs

prop_reverseFromList_toList :: [Int] -> Bool
prop_reverseFromList_toList xs =
  toList (check $ reverseFromList xs) == P.reverse xs

prop_null :: [Int] -> Bool
prop_null xs = P.null xs == null (fromList xs)

------------------------------------------------------------
-- ** cons and snoc

prop_cons :: Int -> [Int] -> Bool
prop_cons x xs = (x:xs) == toList (check (x <| fromList xs))

prop_snoc :: [Int] -> Int -> Bool
prop_snoc xs x = (xs++[x]) == toList (check (fromList xs |> x))

prop_single :: Int -> Bool
prop_single x = [x] == toList (check (singleton x))

prop_cons_fold :: [Int] -> Bool
prop_cons_fold xs = xs == toList (check (foldr (<|) empty xs))
prop_snoc_fold :: [Int] -> Bool
prop_snoc_fold xs = xs == toList (check (foldl (|>) empty xs))

prop_mixed :: [Either Int Int] -> Bool
prop_mixed acts =
    toL (interp cLeft ([],[]) cRight acts) == toList (check $ interp (<|) empty (|>) acts)
  where interp l !curr r ( Left x : xs) = interp l (x `l` curr) r xs
        interp l !curr r (Right x : xs) = interp l (curr `r` x) r xs
        interp l !curr r [] = curr
        x `cLeft` (xs, ys) = (x:xs, ys)
        (xs, ys) `cRight` x = (xs, x:ys)
        toL :: ([Int],[Int]) -> [Int]
        toL (xs, ys) = xs ++ P.reverse ys

------------------------------------------------------------
-- ** length

prop_length :: [()] -> Bool
prop_length xs = P.length xs == length (fromList xs)

prop_length0 :: [()] -> Bool
prop_length0 xs = (length sq == 0) == (null sq)
  where sq = fromList xs

------------------------------------------------------------
-- ** head, tail, viewl, init, last, viewr

prop_head :: [Int] -> Bool
prop_head [] = True
prop_head xs = P.head xs == head (fromList xs)

prop_tail :: [Int] -> Bool
prop_tail [] = True
prop_tail xs = P.tail xs == toList (check $ tail (fromList xs))

prop_viewl :: [Int] -> Bool
prop_viewl xs =
  case viewl (fromList xs) of
    EmptyL -> P.null xs
    x :< s -> P.head xs == x && P.tail xs == toList s

prop_init :: [Int] -> Bool
prop_init [] = True
prop_init xs = P.init xs == toList (init (fromList xs))

prop_last :: [Int] -> Bool
prop_last [] = True
prop_last xs = P.last xs == last (check $ fromList xs)

prop_viewr :: [Int] -> Bool
prop_viewr xs =
  case viewr (fromList xs) of
    EmptyR -> P.null xs
    s :> x -> P.last xs == x && P.init xs == toList s

------------------------------------------------------------
-- ** Equality and ordering

prop_reflexive :: [Int] -> Bool
prop_reflexive xs = fromList xs == fromList xs

prop_reflexive_folded :: [Int] -> Bool
prop_reflexive_folded xs = fromList xs == foldr (<|) empty xs

prop_equality :: [Int] -> [Int] -> Bool
prop_equality xs ys = (xs == ys) == (fromList xs == fromList ys)

prop_le_reflexive :: [Int] -> Bool
prop_le_reflexive xs = fromList xs <= fromList xs

prop_lt_nonreflexive :: [Int] -> Bool
prop_lt_nonreflexive xs = not (fromList xs < fromList xs)

prop_le :: [Int] -> [Int] -> Bool
prop_le xs ys = (xs <= ys) == (fromList xs <= fromList ys)

------------------------------------------------------------
-- ** reverse, inits, tails, fmap

prop_reverse :: [Int] -> Bool
prop_reverse xs = P.reverse xs == toList (reverse (fromList xs))

prop_inits :: [Int] -> Bool
prop_inits xs = L.inits xs == fmap (toList . check) (toList $ inits $ fromList xs)

prop_tails :: [Int] -> Bool
prop_tails xs = L.tails xs == fmap (toList . check) (toList $ tails $ fromList xs)

prop_fmap :: [Int] -> Blind (Int -> Int) -> Bool
prop_fmap xs (Blind f) = fmap f xs == toList (check (fmap f (fromList xs)))

prop_mapWithIndex :: [Int] -> Blind (Int -> Int -> Int) -> Bool
prop_mapWithIndex xs (Blind f) =
  zipWith f [0..] xs == toList (check (mapWithIndex f (fromList xs)))

------------------------------------------------------------
-- ** append, index, take, drop

prop_append :: [Int] -> [Int] -> Bool
prop_append xs ys = (xs ++ ys) == toList (check (fromList xs >< fromList ys))

-- Test cases where we're not creating intermediate results by consing.
-- The big idea here is to create more complex internal tree structures
-- and make sure those don't yield wrong results.
prop_concat_fold2 :: [[Int]] -> Bool
prop_concat_fold2 xss =
  concat xss == toList (check (fold2 (><) empty (fmap fromList xss)))

fold2 :: (a -> a -> a) -> a -> [a] -> a
fold2 op e [] = e
fold2 op e [r] = r
fold2 op e xs = fold2 op e (f2 xs)
  where f2 (a:b:xs) = op a b : f2 xs
        f2 xs = xs

prop_take :: [Int] -> Bool
prop_take xs =
  and [ P.take i xs == toList (check (take i q)) | i <- [-1 .. length q + 1] ]
  where q = fromList xs

prop_drop :: [Int] -> Bool
prop_drop xs =
  and [ P.drop i xs == toList (check (drop i q)) | i <- [-1 .. length q + 1] ]
  where q = fromList xs

prop_splitAt :: [Int] -> Bool
prop_splitAt xs =
  and [ (take i q, drop i q) == check2 (splitAt i q) | i <- [-1 .. length q + 1] ]
  where q = fromList xs
        check2 (a,b) = (check a, check b)

------------------------------------------------------------
-- ** Element access
prop_index :: [Int] -> Bool
prop_index xs = and [(xs!!i) == index q i | i <- [0 .. length q - 1]]
  where q = fromList xs

prop_adjust :: Blind (Int -> Int) -> [Int] -> Bool
prop_adjust (Blind f) xs =
  and [(l ++ f e : r) == toList (check (adjust f i q)) |
       i <- [0 .. length q - 1],
       let (l, e : r) = P.splitAt i xs]
  where q = fromList xs

prop_update :: [Int] -> Int -> Bool
prop_update xs v =
  and [(l ++ v : r) == toList (check (update i v q)) |
       i <- [0 .. length q - 1],
       let (l, e : r) = P.splitAt i xs]
  where q = fromList xs

------------------------------------------------------------
-- ** Replication

prop_replicate :: [()] -> Bool
prop_replicate xs =
  toList r == xs && length (check r) == n
  where n = P.length xs
        r = replicate n ()

prop_replicateA :: [()] -> Bool
prop_replicateA xs =
  toList r == xs && length (check r) == n && s == n
  where n = P.length xs
        (r, Sum s) = runWriter . unwrapMonad . replicateA n $
                     WrapMonad (tell (Sum 1))

prop_replicateM :: [()] -> Bool
prop_replicateM xs =
  toList r == xs && length (check r) == n && s == n
  where n = P.length xs
        (r, Sum s) = runWriter . replicateM n $ tell (Sum 1)

------------------------------------------------------------
-- ** Iterative construction

prop_iterateN :: [()] -> Bool
prop_iterateN xs =
  toList (check (iterateN n (1+) 1)) == [1..n]
  where n = P.length xs

prop_unfoldr :: [()] -> Bool
prop_unfoldr xs =
  toList (check (unfoldr (\i -> if i==0 then Nothing else Just (i, i-1)) n)) == [1..n]
  where n = P.length xs

prop_unfoldl :: [()] -> Bool
prop_unfoldl xs =
  toList (check (unfoldl (\i -> if i > n then Nothing else Just (i+1, i)) 1)) == [1..n]
  where n = P.length xs

------------------------------------------------------------
-- * Scans

prop_scanl :: NonEmptyList Int -> Blind (Int -> Int -> Int) -> Bool
prop_scanl (NonEmpty (x:xs)) (Blind f) =
  L.scanl f x xs == toList (check (scanl f x (fromList xs)))

prop_scanl1 :: [Int] -> Blind (Int -> Int -> Int) -> Bool
prop_scanl1 xs (Blind f) =
  L.scanl1 f xs == toList (check (scanl1 f (fromList xs)))

prop_scanr :: NonEmptyList Int -> Blind (Int -> Int -> Int) -> Bool
prop_scanr (NonEmpty (x:xs)) (Blind f) =
  L.scanr f x xs == toList (check (scanr f x (fromList xs)))

prop_scanr1 :: [Int] -> Blind (Int -> Int -> Int) -> Bool
prop_scanr1 xs (Blind f) =
  L.scanr1 f xs == toList (check (scanr1 f (fromList xs)))

------------------------------------------------------------
-- * All tests.
-- | Frustratingly, if you forget one, you lose.

tests :: [Test]
tests =
  [
    testGroup "Empty, toList, fromList" [
      testProperty "empty is null" prop_empty,
      testProperty "fromList/toList" prop_fromList_toList,
      testProperty "reverseFromList/toList" prop_reverseFromList_toList,
      testProperty "null" prop_null
    ],
    testGroup "Cons and snoc" [
      testProperty "<| conses" prop_cons,
      testProperty "|> snocs" prop_snoc,
      testProperty "singleton" prop_single,
      testProperty "toList is foldr <|" prop_cons_fold,
      testProperty "toList is foldl |>" prop_snoc_fold,
      testProperty "mixed cons and snoc" prop_mixed
    ],
    testGroup "lengths" [
      testProperty "length" prop_length,
      testProperty "length and null" prop_length0
    ],
    testGroup "head, tail, init, last" [
      testProperty "head" prop_head,
      testProperty "tail" prop_tail,
      testProperty "viewl" prop_viewl,
      testProperty "init" prop_init,
      testProperty "last" prop_last,
      testProperty "viewr" prop_viewr
    ],
    testGroup "Equality" [
      testProperty "reflexive" prop_reflexive,
      testProperty "reflexive_folded" prop_reflexive_folded,
      testProperty "equality" prop_equality,
      testProperty "<= reflexive" prop_le_reflexive,
      testProperty "< non-reflexive" prop_lt_nonreflexive,
      testProperty "<= vs list" prop_le
    ],
    testGroup "reverse, inits, tails" [
      testProperty "reverse" prop_reverse,
      testProperty "inits" prop_inits,
      testProperty "tails" prop_tails,
      testProperty "fmap" prop_fmap,
      testProperty "mapWithIndex" prop_mapWithIndex
    ],
    testGroup "append, take, drop" [
      testProperty "append" prop_append,
      testProperty "appends" prop_concat_fold2,
      testProperty "take" prop_take,
      testProperty "drop" prop_drop,
      testProperty "splitAt" prop_splitAt
    ],
    testGroup "Element access" [
      testProperty "index" prop_index,
      testProperty "adjust" prop_adjust,
      testProperty "update" prop_update
    ],
    testGroup "replication" [
      testProperty "replicate" prop_replicate,
      testProperty "replicateA" prop_replicateA,
      testProperty "replicateM" prop_replicateM
    ],
    testGroup "Iterative construction" [
      testProperty "iterateN" prop_iterateN,
      testProperty "unfoldr" prop_unfoldr,
      testProperty "unfoldl" prop_unfoldl
    ],
    testGroup "Scans" [
      testProperty "scanl" prop_scanl,
      testProperty "scanl1" prop_scanl1,
      testProperty "scanr" prop_scanr,
      testProperty "scanr1" prop_scanr1
    ]
  ]

main :: IO ()
main = defaultMain tests
