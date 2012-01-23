{-# LANGUAGE BangPatterns #-}

-- | Tests for Data.FastSequence.  We test functions by comparing them to their list
-- equivalents.

module Main(main) where

import Prelude hiding ( null, reverse, length, head, tail, init, last )
import qualified Prelude as P
import qualified Data.List as L
import Data.FastSequence
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
-- ** head, tail, init, last

prop_head :: [Int] -> Bool
prop_head [] = True
prop_head xs = P.head xs == head (fromList xs)

prop_tail :: [Int] -> Bool
prop_tail [] = True
prop_tail xs = P.tail xs == toList (check $ tail (fromList xs))

prop_init :: [Int] -> Bool
prop_init [] = True
prop_init xs = P.init xs == toList (init (fromList xs))

prop_last :: [Int] -> Bool
prop_last [] = True
prop_last xs = P.last xs == last (check $ fromList xs)

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

prop_fmap :: [Int] -> Int -> Bool
prop_fmap xs x = fmap (x+) xs == toList (check (fmap (x+) (fromList xs)))

------------------------------------------------------------
-- ** append, index, take, drop

prop_append :: [Int] -> [Int] -> Bool
prop_append xs ys = (xs ++ ys) == toList (check (fromList xs >< fromList ys))

-- Test cases where we're not creating intermediate results by consing.
prop_concat_fold2 :: [[Int]] -> Bool
prop_concat_fold2 xss =
  concat xss == toList (check (fold2 (><) empty (fmap fromList xss)))

fold2 :: (a -> a -> a) -> a -> [a] -> a
fold2 op e [] = e
fold2 op e [r] = r
fold2 op e xs = fold2 op e (f2 xs)
  where f2 (a:b:xs) = op a b : f2 xs
        f2 xs = xs

prop_index :: [Int] -> NonNegative Int -> Property
prop_index xs (NonNegative i) = (i < length q) ==> ((xs!!i) == index q i)
  where q = fromList xs

------------------------------------------------------------
-- * All tests.
-- | Frustratingly, if you forget one, you lose.

tests :: [Test]
tests =
  [
    -- empty & to/from
    testGroup "Empty, toList, fromList" [
      testProperty "empty is null" prop_empty,
      testProperty "fromList/toList" prop_fromList_toList,
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
      testProperty "init" prop_init,
      testProperty "last" prop_last
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
      testProperty "fmap" prop_fmap
    ],
    testGroup "append, take, drop" [
      testProperty "append" prop_append,
      testProperty "appends" prop_concat_fold2,
      testProperty "index" prop_index
    ]
  ]

main :: IO ()
main = defaultMain tests
