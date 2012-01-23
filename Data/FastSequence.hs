{-# LANGUAGE BangPatterns #-}
module WideSequence(
    empty, singleton, (|>), (<|), fromList, toList, null, length,
    head, tail, init, last, ViewL(..), viewl, ViewR(..), viewr, reverse,
    pretty, pp
    ) where
import Prelude hiding ( null, reverse, length, head, tail, init, last )
import qualified Prelude as P
import Data.List(foldl')
import qualified Data.Vector as N

type Node a = N.Vector a
type Size = Int
data Sized a = Sized { size :: !Int, datum :: !a }
  deriving (Show)

data Seq a =
    Simple !(Node a)
  | Root { left :: !(Node a),
           down :: !(Seq (Node a)),
           right :: !(Node a) }
  deriving (Show)

-- Symmetric 0-copy split
splitNode :: Node a -> Int -> (Node a, Node a)
splitNode n i = (N.take i n, N.drop i n)

-- Split for R, counting from left, copying left
splitRNode :: Node a -> Int -> (Node a, Node a)
splitRNode n i =
  case splitNode n i of
    (d, r) -> (N.force d, r)

-- Split for L, counting from right, copying right
splitLNode :: Node a -> Int -> (Node a, Node a)
splitLNode n i =
  case splitNode n (N.length n - i) of
    (l, d) -> (l, N.force d)

maxInner :: Int
maxInner = 8

maxFringe :: Int
maxFringe = 12

maxSimple :: Int
maxSimple = maxFringe

empty :: Seq a
empty = Simple N.empty

singleton :: a -> Seq a
singleton = Simple . N.singleton

(<|) :: a -> Seq a -> Seq a
a <| Simple m
  | N.length m < maxSimple = Simple (N.cons a m)
  | otherwise =
    case splitLNode m maxInner of
      (l, r) -> Root (N.cons a l) empty r
a <| Root l d r
  | N.length l < maxFringe = Root (N.cons a l) d r
  | otherwise =
    case splitLNode l maxInner of
      (l', d') -> Root (N.cons a l') (d' <| d) r

(|>) :: Seq a -> a -> Seq a
Simple m |> b
  | N.length m < maxSimple = Simple (N.snoc m b)
  | otherwise =
    case splitRNode m maxInner of
      (l, r) -> Root l empty (N.snoc r b)
Root l d r |> b
  | N.length r < maxFringe = Root l d (N.snoc r b)
  | otherwise =
    case splitRNode r maxInner of
      (d', r') -> Root l (d |> d') (N.snoc r' b)

{-
(><) :: Seq a -> Seq a -> Seq a
-}

fromList :: [a] -> Seq a
fromList = foldl' (|>) empty

null :: Seq a -> Bool
null (Simple m) = N.null m
null _ = False

length :: Seq a -> Int
length (Simple m) = N.length m
length (Root l d r) =
    lengthf (\ !n d -> N.length d + n) (N.length l + N.length r) d

lengthf :: (Int -> a -> Int) -> Int -> Seq a -> Int
lengthf f !n (Simple m) = N.foldl' f n m
lengthf f !n (Root l d r) = lengthf f' (f' (f' n l) r) d
  where f' !n d = N.foldl' f n d

data ViewL a = EmptyL
             | a :< Seq a
viewl :: Seq a -> ViewL a
viewl (Simple m)
  | N.null m = EmptyL
  | otherwise = N.head m :< Simple (N.tail m)
viewl (Root l d r) =
  N.head l :< (
    if N.length l > 1 then Root (N.tail l) d r
    else case viewl d of
           l' :< d' -> Root l' d' r
           EmptyL   -> Simple r)

head t =
  case viewl t of
    EmptyL -> error "head empty"
    a :< _ -> a

tail t =
  case viewl t of
    EmptyL -> error "tail empty"
    _ :< r -> r

data ViewR a = EmptyR
             | Seq a :> a
viewr :: Seq a -> ViewR a
viewr (Simple m)
  | N.null m = EmptyR
  | otherwise = Simple (N.init m) :> N.last m
viewr (Root l d r) =
  ( if N.length r > 1 then Root l d (N.init r)
    else case viewr d of
           d' :> r' -> Root l d' r'
           EmptyR   -> Simple l) :> N.last r

init t =
  case viewr t of
    EmptyR -> error "init empty"
    r :> _ -> r

last t =
  case viewr t of
    EmptyR -> error "last empty"
    _ :> b -> b

{-
index :: Seq a -> Int -> a
adjust :: (a -> a) -> Int -> Seq a -> Seq a
update :: Int -> a -> Seq a -> Seq a
take :: Int -> Seq a -> Seq a
drop :: Int -> Seq a -> Seq a
splitAt :: Int -> Seq a -> (Seq a, Seq a)
-}

reverse :: Seq a -> Seq a
reverse = reversef N.reverse

reversef :: (Node a -> Node a) -> Seq a -> Seq a
reversef f (Simple m) = Simple (f m)
reversef f (Root l d r) = Root (f r) (reversef f' d) (f l)
  where f' = N.map f . N.reverse

toList :: Seq a -> [a]
toList s =
  case viewl s of
    EmptyL -> []
    a :< s' -> a : toList s'

-- This pretty printer is cheap and cheerful (eg not written in ShowS style)
pretty :: Show a => Seq a -> String
pretty = prettyf (show . N.toList)

prettyr :: Show a => (a -> String) -> Seq a -> String
prettyr f t = "(" ++ prettyf f' t ++ ")"
  where f' xs = "[" ++ drop 1 (N.foldr (\d r -> "," ++ f d ++ r) "" xs) ++ "]"

prettyf :: Show a => (Node a -> String) -> Seq a -> String
prettyf f (Simple m) = "S " ++ f m
prettyf f (Root l d r) = "R " ++ f l ++ " " ++ prettyr f d ++ " " ++ f r

-- pretty print
pp :: Show a => Seq a -> IO ()
pp = putStrLn . pretty