{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, PatternGuards #-}
module Data.FastSequence(
    empty, singleton, (|>), (<|), fromList, toList, null, length,
    head, tail, init, last, ViewL(..), viewl, ViewR(..), viewr,
    reverse, tails, inits, (><),
    index,
    pretty, pp, check
    ) where
import Prelude hiding ( null, reverse, length, head, tail, init, last )
import qualified Prelude as P
import Data.List(foldl')
import qualified Data.Vector as N

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

-- Size describes the count of items in a sequence.
type Size = Int
type Sizeof a = a -> Int

-- Breadth describes the width of a tree node.
type Breadth = Int

data Node a = Node { size :: !Size, datum :: !(N.Vector a) }

instance (Show a) => Show (Node a) where
  show = showN

data Seq a =
    Simple !(Node a)
  | Root !Size !(Node a) (Seq (Node a)) !(Node a)

instance (Show a) => Show (Seq a) where
  show = pretty

------------------------------------------------------------
-- * Instances

instance (Eq a) => Eq (Seq a) where
  -- For the moment we're quite naive here.
  s1 == s2 = length s1 == length s2 && toList s1 == toList s2

instance (Ord a) => Ord (Seq a) where
  -- Also quite naive
  compare s1 s2 = compare (toList s1) (toList s2)

------------------------------------------------------------
-- Some internals.  First, node manipulation.

node :: Sizeof a -> N.Vector a -> Node a
node so n = Node (N.foldl' (\s a -> s + so a) 0 n) n

-- Symmetric 0-copy split
splitNode :: N.Vector a -> Breadth -> (N.Vector a, N.Vector a)
splitNode n b = (N.take b n, N.drop b n)

-- Split for R, counting from left, copying left
splitRNode :: Sizeof a -> Node a -> Breadth -> (Node a, Node a)
splitRNode so (Node s n) b =
  case splitNode n b of
    (d, r) -> (node so (N.force d), node so r)

-- Split for L, counting from right, copying right
splitLNode :: Sizeof a -> Node a -> Breadth -> (Node a, Node a)
splitLNode so (Node s n) b =
  case splitNode n (N.length n - b) of
    (l, d) -> (node so l, node so (N.force d))

forceN :: Node a -> Node a
forceN (Node s n) = Node s (N.force n)

consN :: Sizeof a -> a -> Node a -> Node a
consN so a (Node s n) = Node (so a + s) (N.cons a n)

snocN :: Sizeof a -> Node a -> a -> Node a
snocN so (Node s n) a = Node (so a + s) (N.snoc n a)

breadthN :: Node a -> Breadth
breadthN (Node _ n) = N.length n

headN :: Node a -> a
headN (Node _ n) = N.head n

tailN :: Sizeof a -> Node a -> Node a
tailN so (Node s n) = Node (s - so (N.head n)) (N.force (N.tail n))

lastN :: Node a -> a
lastN (Node _ n) = N.last n

initN :: Sizeof a -> Node a -> Node a
initN so (Node s n) = Node (s - so (N.last n)) (N.force (N.init n))

appN :: Node a -> Node a -> Node a
appN (Node s1 n1) (Node s2 n2) = Node (s1+s2) (n1 N.++ n2)

emptyN :: Node a
emptyN = Node 0 N.empty

nullN :: Node a -> Bool
nullN (Node _ n) = N.null n

foldlN' :: (r -> a -> r) -> r -> Node a -> r
foldlN' f z (Node _ n) = N.foldl' f z n

reverseN :: Node a -> Node a
reverseN (Node s n) = Node s (N.reverse n)

instance Functor Node where
  fmap f (Node s n) = Node s (N.map f n)

------------------------------------------------------------
-- Now a constructor for root
root :: Node a -> Seq (Node a) -> Node a -> Seq a
root l m r = Root (size l + length m + size r) l m r

maxInner :: Breadth
maxInner = 8

minInner :: Breadth
minInner = 4

maxFringe :: Breadth
maxFringe = 12

minFringe :: Breadth
minFringe = 2

maxSimple :: Breadth
maxSimple = 15

empty :: Seq a
empty = Simple emptyN

singleton :: a -> Seq a
singleton = Simple . Node 1 . N.singleton

(<|) :: a -> Seq a -> Seq a
a <| sq = cons (const 1) a sq

cons :: Sizeof a -> a -> Seq a -> Seq a
cons so a (Simple m)
  | breadthN m < maxSimple = Simple (consN so a m)
  | otherwise =
    case splitLNode so m maxInner of
      (l, r) -> Root (so a + size m) (consN so a l) empty r
cons so a (Root s l d r)
  | breadthN l < maxFringe = Root (so a + s) (consN so a l) d r
  | otherwise =
    case splitLNode so l maxInner of
      (l', d') -> Root (so a + s) (consN so a l') (cons size d' d) r

(|>) :: Seq a -> a -> Seq a
sq |> a = snoc (const 1) sq a

snoc :: Sizeof a -> Seq a -> a -> Seq a
snoc so (Simple m) b
  | breadthN m < maxSimple = Simple (snocN so m b)
  | otherwise =
    case splitRNode so m maxInner of
      (l, r) -> Root (so b + size m) l empty (snocN so r b)
snoc so (Root s l d r) b
  | breadthN r < maxFringe = Root (so b + s) l d (snocN so r b)
  | otherwise =
    case splitRNode so r maxInner of
      (d', r') -> Root (so b + s) l (snoc size d d') (snocN so r' b)

(><) :: Seq a -> Seq a -> Seq a
sq1 >< sq2 = append (const 1) sq1 sq2

append :: Sizeof a -> Seq a -> Seq a -> Seq a
append so (Simple m1) (Simple m2)
  | breadthN m1 == 0 = Simple m2
  | breadthN m2 == 0 = Simple m1
  | otherwise = simple so (appN m1 m2)
append so (Simple m) (Root s l d r)
  | breadthN m == 0 = Root s l d r
  | otherwise = midL so (s + size m) (appN m l) d r
append so (Root s l d r) (Simple m)
  | breadthN m == 0 = Root s l d r
  | otherwise = midR so (s + size m) l d (appN r m)
append so (Root sl ll dl rl) (Root sr lr dr rr) =
  Root (sl + sr) ll (append size dl (mid so (appN rl lr) dr)) rr

-- midL builds a root from a too-big left Node a, where the root has a left
-- Node a of size at most maxFringe
midL :: Sizeof a -> Size -> Node a -> Seq (Node a) -> Node a -> Seq a
midL so s l d r
  | b <= maxFringe = Root s (forceN l) d r
  | otherwise =
    case splitLNode so l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> midL so s ll (cons size lr d) r
  where b = breadthN l

-- mid is midL that pushes everything into "d"
mid :: Sizeof a -> Node a -> Seq (Node a) -> Seq (Node a)
mid so l d
  | b <= maxInner = cons size (forceN l) d
  | otherwise =
    case splitLNode so l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> mid so ll (cons size lr d)
  where b = breadthN l

-- midR pastes Seq (Node a) onto a too-big (Node a)
midR :: Sizeof a -> Size -> Node a -> Seq (Node a) -> Node a -> Seq a
midR so s l d r
  | b <= maxFringe = Root s l d (forceN r)
  | otherwise =
    case splitRNode so r (((b+1) `quot` 2) `min` maxInner) of
      (rl, rr) -> midR so s l (snoc size d rl) rr
  where b = breadthN r

-- A meta-constructor for possibly-too-big Nodes
simple :: Sizeof a -> Node a -> Seq a
simple so m
  | b <= maxSimple = Simple m
  | otherwise =
    case splitRNode so m (((b+1) `quot` 2) `min` maxInner) of
      (l, r) -> midR so (size m) l empty r
  where b = breadthN m

null :: Seq a -> Bool
null (Simple m) = nullN m
null _ = False

length :: Seq a -> Size
length (Simple m) = size m
length (Root s l d r) = s

{-
    lengthf (\ !n d -> breadthN d + n) (breadthN l + breadthN r) d

lengthf :: (Int -> a -> Int) -> Int -> Seq a -> Int
lengthf f !n (Simple m) = foldlN' f n m
lengthf f !n (Root s l d r) = lengthf f' (f' (f' n l) r) d
  where f' !n d = foldlN' f n d
-}

data ViewL a = EmptyL
             | a :< Seq a
             deriving (Eq, Ord)

viewl :: Seq a -> ViewL a
viewl = viewl' (const 1)

viewl' :: Sizeof a -> Seq a -> ViewL a
viewl' so (Simple m)
  | nullN m = EmptyL
  | otherwise = headN m :< Simple (tailN so m)
viewl' so (Root s l d r) =
  hn :< (
    if breadthN l > minFringe then Root (s - so hn) tn d r
    else case viewl' size d of
           l' :< d' -> Root (s - so hn) (appN tn l') d' r
           EmptyL   -> Simple (appN tn r))
  where hn = headN l
        tn = tailN so l

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
             deriving (Eq, Ord)

viewr :: Seq a -> ViewR a
viewr = viewr' (const 1)

viewr' :: Sizeof a -> Seq a -> ViewR a
viewr' so (Simple m)
  | nullN m = EmptyR
  | otherwise = Simple (initN so m) :> lastN m
viewr' so (Root s l d r) =
  ( if breadthN r > minFringe then Root (s - so ln) l d nn
    else case viewr' size d of
           d' :> r' -> Root (s - so ln) l d' (appN r' nn)
           EmptyR   -> Simple (appN l nn)) :> ln
  where ln = lastN r
        nn = initN so r

init t =
  case viewr t of
    EmptyR -> error "init empty"
    r :> _ -> r

last t =
  case viewr t of
    EmptyR -> error "last empty"
    _ :> b -> b

------------------------------------------------------------
-- * Indexing and indexed operations

index :: (Show a) => Seq a -> Int -> a
index m i | i < 0 || i >= length m =
  error "FastSequence.index: index out of bounds"
index (Simple m) i = datum m N.! i
index m i = fst (index' (const 1) m i)

-- index' may be indexing a deep Seq (Node a), in which
-- case many indices occur in a single element.  As a result
-- we return not only the value indexed, but the residual
-- index as well.  That way the caller (the third clause below)
-- can then index into the resulting node.
index' :: (Show a) => Sizeof a -> Seq a -> Int -> (a, Int)
index' so (Simple m) i = indexN so m i
index' so (Root s l d r) i
  | i < sl = indexN so l i
  | i < sld = uncurry (indexN so) (index' size d (i - sl))
  | otherwise = indexN so r (i - sld)
  where sl = size l
        sld = sl + length d

-- Again, we might have a Node (Node a) here, in which
-- case each element will cover multiple indices.  As a
-- result we return the residual index, so the caller can
-- index into the result if necessary.
indexN :: (Show a) => Sizeof a -> Node a -> Int -> (a, Int)
indexN so n@(Node s v) i = loop 0 i
  where loop position i
          | i < se = (e, i)
          | position + 1 == breadthN n = error ("indexN " ++ show n ++ " " ++ show i)
          | otherwise = loop (position + 1) (i - se)
          where e = v N.! position
                se = so e

{-
adjust :: (a -> a) -> Int -> Seq a -> Seq a
update :: Int -> a -> Seq a -> Seq a
take :: Int -> Seq a -> Seq a
drop :: Int -> Seq a -> Seq a
splitAt :: Int -> Seq a -> (Seq a, Seq a)
-}

------------------------------------------------------------
-- * List-like utilities

reverse :: Seq a -> Seq a
reverse = reversef reverseN

reversef :: (Node a -> Node a) -> Seq a -> Seq a
reversef f (Simple m) = Simple (f m)
reversef f (Root s l d r) = Root s (f r) (reversef f' d) (f l)
  where f' = fmap f . reverseN

tails :: Seq a -> Seq (Seq a)
tails sq =
  case viewl sq of
    EmptyL -> singleton sq
    _ :< sq' -> sq <| tails sq'

inits :: Seq a -> Seq (Seq a)
inits sq =
  case viewr sq of
    EmptyR -> singleton sq
    sq' :> _ -> inits sq' |> sq

------------------------------------------------------------
-- * fromList and toList

fromList :: [a] -> Seq a
fromList xs = fromListBody (const 1) xs

fromListBody :: Sizeof a -> [a] -> Seq a
fromListBody so xs
  -- We use a lazy length-checking idiom here, but compute
  -- the length when we discover xs is short.
  | P.null (P.drop maxSimple xs) = Simple (node so (N.fromList xs))
  | P.null (P.drop (2 * maxFringe) xs) =
    root (node so (N.fromList l)) empty (node so (N.fromList r))
  | otherwise = root lf d lr
  where b = P.length xs
        (l, r) = P.splitAt (b `quot` 2) xs
        (lf : ns) = nests so xs
        d :> lr = viewr' size $ fromListBody size ns

nests :: Sizeof a -> [a] -> [Node a]
nests so [] = []
nests so xs =
  case P.splitAt maxInner xs of
    (nd, xs')
      | P.null xs' -> [node so (N.fromList nd)]
      | P.null (P.drop (minInner-1) xs') ->
         case P.splitAt (P.length xs - minInner) xs of
           (l,r) -> [node so (N.fromList l), node so (N.fromList r)]
      | otherwise -> node so (N.fromList nd) : nests so xs'

toList :: Seq a -> [a]
toList s =
  case viewl s of
    EmptyL -> []
    a :< s' -> a : toList s'

------------------------------------------------------------
-- * Functor

instance Functor Seq where
  fmap f (Simple m) = Simple (fmap f m)
  fmap f (Root s l d r) =
    Root s (fmap f l) (fmap (fmap f) d) (fmap f r)

------------------------------------------------------------
-- * Pretty printing

-- This pretty printer is cheap and cheerful (eg not written in ShowS style)
pretty :: Show a => Seq a -> String
pretty = prettyf showN

prettyr :: Show a => (a -> String) -> Seq a -> String
prettyr f t = "(" ++ prettyf (showNInner f) t ++ ")"

showN :: (Show a) => Node a -> String
showN (Node s n) = "<" ++ show s ++ ">" ++ show (N.toList n)

showNInner :: (a -> String) -> Node a -> String
showNInner f (Node n s) =
  "<" ++ show n ++ ">[" ++ drop 1 (N.foldr (\d r -> "," ++ f d ++ r) "" s) ++ "]"

prettyf :: Show a => (Node a -> String) -> Seq a -> String
prettyf f (Simple m) = "S " ++ f m
prettyf f (Root s l d r) = "R<" ++ show s ++ "> " ++ f l ++ " " ++ prettyr f d ++ " & " ++ f r

-- pretty print
pp :: Show a => Seq a -> IO ()
pp = putStrLn . pretty

------------------------------------------------------------
-- Invariant checker.  Passes through the value if OK, otherwise calls error.
naiveSizeof :: Sizeof a -> Sizeof (Node a)
naiveSizeof so m = size (node so (datum m))

check :: (Show a) => Seq a -> Seq a
check a = checkS (const 1) a

checkS :: (Show a) => Sizeof a -> Seq a -> Seq a
checkS so a
  | Just bug <- ok so showN a =
    error ("Violates invariant:\n" ++ bug ++ "\n\nData: " ++ pretty a)
  | otherwise = a

-- OK is sort of the reverse of the usual Maybe monad; it either succeeds silently,
-- or fails with an error message.
ok :: (Show a) => Sizeof a -> (Node a -> String) -> Seq a -> Maybe String
ok so pr (Simple m) = okN so pr 0 maxSimple m
ok so pr n@(Root s l d r)
  | Just lerr <- okN so pr minFringe maxFringe l = Just lerr
  | Just derr <- ok (naiveSizeof so) (showNInner pr) d = Just derr
  | Just rerr <- okN so pr minFringe maxFringe r = Just rerr
  | computedSz /= s =
    Just ("Computed size " ++ show computedSz ++ " different: " ++ prettyf pr n)
  | otherwise = Nothing
  where computedSz = size l + length d + size r

okN :: Sizeof a -> (Node a -> String) -> Size -> Size -> Node a -> Maybe String
okN so pr mn mx m
  | breadthN m > mx = Just ("Node too big: " ++ pr m)
  | breadthN m < mn = Just ("Node too small: " ++ pr m)
  | computedSz /= size m =
    Just ("Computed size " ++ show computedSz ++ " different: " ++ pr m)
  | otherwise = Nothing
  where computedSz = naiveSizeof so m
