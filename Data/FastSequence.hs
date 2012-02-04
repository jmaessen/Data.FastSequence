{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Data.FastSequence(
    empty, singleton, (|>), (<|), fromList, toList, null, length,
    head, tail, init, last, ViewL(..), viewl, ViewR(..), viewr,
    reverse, tails, inits, (><),
    index, adjust, update, take, drop,
    pretty, pp, check
    ) where
import Prelude hiding ( null, reverse, length, head, tail, init, last, take, drop, foldr )
import qualified Prelude as P
import Data.List(foldl')
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import Data.Typeable(Typeable1(..))
import qualified Data.Vector as N
import Debug.Trace(trace)

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

newtype Seq a = Seq { unSeq :: FTree (Elem a) }
  deriving (Functor, Foldable, Traversable)

instance (Show a) => Show (Seq a) where
  showsPrec p (Seq s) = showsPrec p s  -- Temporary, for debugging.

-- Breadth describes the width of a tree node.
type Breadth = Int

data Node a = Node { nodeSize :: !Size, datum :: !(N.Vector a) }
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show a) => Show (Node a) where
  show = showN

data FTree a =
    Simple !(Node a)
  | Root !Size !(Node a) (FTree (Node a)) !(Node a)
  deriving (Foldable, Traversable)

instance (Show a) => Show (FTree a) where
  show = prettyf showN

------------------------------------------------------------
-- * Sized objects

-- Size describes the count of items in a sequence.
type Size = Int

-- For a while we weren't using Sized here, but were passing a size
-- function instead.  But local dictionary specialization ought to
-- apply if we use the type class, making that far more efficient
-- after inlining.
newtype Elem a = Elem { unElem :: a }
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show a => Show (Elem a) where
  showsPrec p (Elem e) = showsPrec p e  -- Don't show the wrappers.

class Sized a where
  size :: a -> Size
  sizeN :: N.Vector a -> Size
  sizeN = N.foldl' (\s a -> s + size a) 0

instance Sized (Elem a) where
  size _ = 1
  sizeN = N.length

instance Sized (Node a) where
  size = nodeSize

instance Sized (FTree a) where
  size (Simple m) = size m
  size (Root s _ _ _) = s

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

node :: (Sized a) => N.Vector a -> Node a
node n = Node (sizeN n) n

-- Symmetric 0-copy split
splitNode :: N.Vector a -> Breadth -> (N.Vector a, N.Vector a)
splitNode n b = (N.take b n, N.drop b n)

-- Split for R, counting from left, copying left
splitRNode :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitRNode (Node s n) b =
  case splitNode n b of
    (d, r) -> (node (N.force d), node r)

-- Split for L, counting from right, copying right
splitLNode :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitLNode (Node s n) b =
  case splitNode n (N.length n - b) of
    (l, d) -> (node l, node (N.force d))

forceN :: Node a -> Node a
forceN (Node s n) = Node s (N.force n)

consN :: (Sized a) => a -> Node a -> Node a
consN a (Node s n) = Node (size a + s) (N.cons a n)

snocN :: (Sized a) => Node a -> a -> Node a
snocN (Node s n) a = Node (size a + s) (N.snoc n a)

breadth :: Node a -> Breadth
breadth (Node _ n) = N.length n

headN :: Node a -> a
headN (Node _ n) = N.head n

tailN :: (Sized a) => Node a -> Node a
tailN (Node s n) = Node (s - size (N.head n)) (N.force (N.tail n))

lastN :: Node a -> a
lastN (Node _ n) = N.last n

initN :: (Sized a) => Node a -> Node a
initN (Node s n) = Node (s - size (N.last n)) (N.force (N.init n))

appN :: Node a -> Node a -> Node a
appN (Node s1 n1) (Node s2 n2) = Node (s1+s2) (n1 N.++ n2)

nullN :: Node a -> Bool
nullN (Node s _) = s == 0

foldlN' :: (r -> a -> r) -> r -> Node a -> r
foldlN' f z (Node _ n) = N.foldl' f z n

reverseN :: Node a -> Node a
reverseN (Node s n) = Node s (N.reverse n)

fromListN :: (Sized a) => [a] -> Node a
fromListN xs = node (N.fromList xs)

{-# INLINE adjustN #-}
adjustN :: (a -> a) -> Breadth -> Node a -> Node a
adjustN f i (Node s v) = Node s (v N.// [(i, f (v N.! i))])

------------------------------------------------------------
-- Now a constructor for root
root :: Node a -> FTree (Node a) -> Node a -> FTree a
root l m r = Root (size l + size m + size r) l m r

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

emptyTree :: FTree a
emptyTree = Simple (Node 0 N.empty)

empty :: Seq a
empty = Seq emptyTree

singleton :: a -> Seq a
singleton = Seq . Simple . Node 1 . N.singleton . Elem

(<|) :: a -> Seq a -> Seq a
a <| Seq sq = Seq (cons (Elem a) sq)

cons :: (Sized a) => a -> FTree a -> FTree a
cons a (Simple m)
  | breadth m < maxSimple = Simple (consN a m)
  | otherwise =
    case splitLNode m maxInner of
      (l, r) -> Root (size a + size m) (consN a l) emptyTree r
cons a (Root s l d r)
  | breadth l < maxFringe = Root (size a + s) (consN a l) d r
  | otherwise =
    case splitLNode l maxInner of
      (l', d') -> Root (size a + s) (consN a l') (cons d' d) r

(|>) :: Seq a -> a -> Seq a
Seq sq |> a = Seq (snoc sq (Elem a))

snoc :: (Sized a) => FTree a -> a -> FTree a
snoc (Simple m) b
  | breadth m < maxSimple = Simple (snocN m b)
  | otherwise =
    case splitRNode m maxInner of
      (l, r) -> Root (size b + size m) l emptyTree (snocN r b)
snoc (Root s l d r) b
  | breadth r < maxFringe = Root (size b + s) l d (snocN r b)
  | otherwise =
    case splitRNode r maxInner of
      (d', r') -> Root (size b + s) l (snoc d d') (snocN r' b)

(><) :: Seq a -> Seq a -> Seq a
Seq sq1 >< Seq sq2 = Seq (append sq1 sq2)

append :: (Sized a) => FTree a -> FTree a -> FTree a
append (Simple m1) (Simple m2)
  | breadth m1 == 0 = Simple m2
  | breadth m2 == 0 = Simple m1
  | otherwise = simple (appN m1 m2)
append (Simple m) (Root s l d r)
  | breadth m == 0 = Root s l d r
  | otherwise = midL (s + size m) (appN m l) d r
append (Root s l d r) (Simple m)
  | breadth m == 0 = Root s l d r
  | otherwise = midR (s + size m) l d (appN r m)
append (Root sl ll dl rl) (Root sr lr dr rr) =
  Root (sl + sr) ll (append dl (mid (appN rl lr) dr)) rr

-- midL builds a root from a too-big left Node a, where the root has a left
-- Node a of size at most maxFringe
midL :: (Sized a) => Size -> Node a -> FTree (Node a) -> Node a -> FTree a
midL s l d r
  | b <= maxFringe = Root s (forceN l) d r
  | otherwise =
    case splitLNode l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> midL s ll (cons lr d) r
  where b = breadth l

-- mid is midL that pushes everything into "d"
mid :: (Sized a) => Node a -> FTree (Node a) -> FTree (Node a)
mid l d
  | b <= maxInner = cons (forceN l) d
  | otherwise =
    case splitLNode l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> mid ll (cons lr d)
  where b = breadth l

-- midR pastes FTree (Node a) onto a too-big (Node a)
midR :: (Sized a) => Size -> Node a -> FTree (Node a) -> Node a -> FTree a
midR s l d r
  | b <= maxFringe = Root s l d (forceN r)
  | otherwise =
    case splitRNode r (((b+1) `quot` 2) `min` maxInner) of
      (rl, rr) -> midR s l (snoc d rl) rr
  where b = breadth r

-- A meta-constructor for possibly-too-big Nodes
simple :: (Sized a) => Node a -> FTree a
simple m
  | b <= maxSimple = Simple m
  | otherwise =
    case splitRNode m (((b+1) `quot` 2) `min` maxInner) of
      (l, r) -> midR (size m) l emptyTree r
  where b = breadth m

null :: Seq a -> Bool
null (Seq (Simple m)) = nullN m
null _ = False

length :: Seq a -> Size
length (Seq s) = size s

data TreeView a = Empty | View a (FTree a)

data ViewL a = EmptyL
             | a :< Seq a
             deriving (Eq, Ord, Show)

viewl :: Seq a -> ViewL a
viewl (Seq s) =
  case viewl' s of
    Empty -> EmptyL
    View (Elem l) t -> l :< Seq t

viewl' :: (Sized a) => FTree a -> TreeView a
viewl' (Simple m)
  | nullN m = Empty
  | otherwise = View (headN m) (Simple (tailN m))
viewl' (Root s l d r) = View hn (rootL (s - size hn) (tailN l) d r)
  where hn = headN l

-- Create a Root node with a potentially undersized l
rootL :: Size -> Node a -> FTree (Node a) -> Node a -> FTree a
rootL s l d r
  | breadth l >= minFringe = Root s l d r
  | otherwise =
    case viewl' d of
      View l' d' -> Root s (appN l l') d' r
      Empty      -> Simple (appN l r)

head :: Seq a -> a
head (Seq (Simple m))
  | nullN m   = error "head empty"
  | otherwise = unElem (headN m)
head (Seq (Root s l d r)) = unElem (headN l)

tail :: Seq a -> Seq a
tail t =
  case viewl t of
    EmptyL -> error "tail empty"
    _ :< r -> r

data ViewR a = EmptyR
             | Seq a :> a
             deriving (Eq, Ord)

viewr :: Seq a -> ViewR a
viewr (Seq s) =
  case viewr' s of
    Empty -> EmptyR
    View (Elem r) t -> Seq t :> r

viewr' :: (Sized a) => FTree a -> TreeView a
viewr' (Simple m)
  | nullN m = Empty
  | otherwise = View (lastN m) (Simple (initN m))
viewr' (Root s l d r) = View ln (rootR (s - size ln) l d (initN r))
  where ln = lastN r

-- Create a Root node with a potentially undersized R
rootR :: Size -> Node a -> FTree (Node a) -> Node a -> FTree a
rootR s l d r
  | breadth r >= minFringe = Root s l d r
  | otherwise =
    case viewr' d of
      View r' d' -> Root s l d' (appN r' r)
      Empty      -> Simple (appN l r)

init :: Seq a -> Seq a
init t =
  case viewr t of
    EmptyR -> error "init empty"
    r :> _ -> r

last :: Seq a -> a
last (Seq (Simple m))
  | nullN m   = error "last empty"
  | otherwise = unElem (lastN m)
last (Seq (Root s l d r)) = unElem (lastN r)

------------------------------------------------------------
-- * Indexing and indexed operations

index :: (Show a) => Seq a -> Size -> a
index !m i | i < 0 = indexErr
index (Seq (Simple m)) i | i < size m = unElem (datum m N.! i)
index (Seq t@(Root s l d r)) i | i < s = unElem (snd (index' t i))
index _ _ = indexErr

indexErr :: a
indexErr = error "FastSequence.index: index out of bounds"

-- index' may be indexing a deep Seq (Node a), in which
-- case many indices occur in a single element.  As a result
-- we return not only the value indexed, but the residual
-- index as well.  That way the caller (the third clause below)
-- can then index into the resulting node.
index' :: (Sized a) => FTree a -> Size -> (Size, a)
index' (Simple m) i = indexN i m
index' (Root s l d r) i
  | i < sl = indexN i l
  | i < sld = uncurry indexN (index' d (i - sl))
  | otherwise = indexN (i - sld) r
  where sl = size l
        sld = sl + size d

-- Again, we might have a Node (Node a) here, in which
-- case each element will cover multiple indices.  As a
-- result we return the residual index, so the caller can
-- index into the result if necessary.
indexN :: (Sized a) => Size ->  Node a -> (Size, a)
indexN i n@(Node s v) = loop 0 i
  where loop position i
          | i < se = (i, e)
          | otherwise = loop (position + 1) (i - se)
          where e = v N.! position
                se = size e

adjust :: (a -> a) -> Size -> Seq a -> Seq a
adjust f i !m | i < 0 = adjustErr
adjust f i (Seq (Simple m))
  | i < size m = Seq (Simple (adjustN (Elem . f . unElem) i m))
adjust f i (Seq t@(Root s l d r))
  | i < s = Seq (adjust' (const (Elem . f . unElem)) i t)
adjust f i m = adjustErr

adjustErr :: a
adjustErr = error "FastSequence.adjust: index out of bounds"

-- We pass the "remaining" index into the adjustment function.
-- This is important for upper levels of the tree, where the adjustment
-- function is actually looking deeper in the current level.
adjust' :: (Sized a) => (Size -> a -> a) -> Size -> FTree a -> FTree a
adjust' f i (Simple m) = Simple (adjustN' f i m)
adjust' f i (Root s l d r)
  | i < sl = Root s (adjustN' f i l) d r
  | i < sld = Root s l (adjust' (adjustN' f) (i - sl) d) r
  | otherwise = Root s l d (adjustN' f (i - sld) r)
  where sl = size l
        sld = sl + size d

adjustN' :: (Sized a) => (Size -> a -> a) -> Size -> Node a -> Node a
adjustN' f i0 n@(Node s v) = loop 0 i0
  where loop position i
          | i < se = adjustN (f i) position n
          | otherwise = loop (position + 1) (i - se)
          where e = v N.! position
                se = size e

update :: Size -> a -> Seq a -> Seq a
update i v !m | i < 0 || i >= length m = updateErr
update i v m = adjust (const v) i m

updateErr :: a
updateErr = error "FastSequence.update: index out of bounds"

take :: Size -> Seq a -> Seq a
take i !sq | i <= 0 = empty
take i sq@(Seq (Simple (Node s v)))
  | i < s = Seq (Simple (Node i (N.take i v)))
take i sq@(Seq t@(Root s l d r))
  | i < s =
    case take' i t of
      (_, r, _) -> Seq r
take i sq = sq

-- Result is (remaining elements to drop, head without those elements,
-- tail element from which elements may possibly be dropped).
take' :: (Sized a) => Size -> FTree a -> (Size, FTree a, a)
take' i (Simple m) = midSimple (takeN' i m)
take' i (Root s l d r)
  | i < sl = midSimple (takeN' i l)
  | i < sld =
    case take' (i - sl) d of
      (i1, d1, r1) ->
        case takeN' i1 r1 of
          (i2, r2, u) -> (i2, rootR (i - i2) l d1 r2, u)
  | otherwise =
    case takeN' (i - sld) r of
      (i', r, u) -> (i', rootR (i - i') l d r, u)
  where sl = size l
        sld = sl + size d

midSimple :: (a, Node b, c) -> (a, FTree b, c)
midSimple (a, m, c) = (a, Simple m, c)

takeN' :: Sized a => Size -> Node a -> (Size, Node a, a)
takeN' i0 n@(Node s v) = loop 0 i0
  where loop position i
          | i < se = (i, Node (i0 - i) (N.take position v), e)
          | otherwise = loop (position + 1) (i - se)
          where e = v N.! position
                se = size e

drop :: Size -> Seq a -> Seq a
drop i sq | i <= 0 = sq
drop i sq@(Seq (Simple (Node s v)))
  | i < s = Seq (Simple (Node (s - i) (N.drop i v)))
drop i sq@(Seq t@(Root s l d r))
  | i < s =
    case drop' i t of
      (_, r, e) -> Seq (cons e r)
drop i sq = empty

-- Result is (remaining elements to drop, tail without leading
-- elements, head element from which elements may possibly be
-- dropped).
drop' :: (Sized a) => Size -> FTree a -> (Size, FTree a, a)
drop' i (Simple m) = midSimple (dropN' i m)
drop' i (Root s l d r)
  | i < sl =
    case dropN' i l of
      (i', l', u) -> (i', rootL (s - i + i' - size u) l' d r, u)
  | i < sld =
    case drop' (i - sl) d of
      (i1, d1, l1) ->
        case dropN' i1 l1 of
          (i2, l2, u) -> (i2, rootL (s - i + i2 - size u) l2 d1 r, u)
  | otherwise = midSimple (dropN' (i - sld) r)
  where sl = size l
        sld = sl + size d

dropN' :: Sized a => Size -> Node a -> (Size, Node a, a)
dropN' i0 n@(Node s v) = loop 0 i0
  where loop position i
          | i < se = (i, Node (s - i0 + i - se) (N.drop (position + 1) v), e)
          | otherwise = loop (position + 1) (i - se)
          where e = v N.! position
                se = size e

{-
splitAt :: Size -> Seq a -> (Seq a, Seq a)
-}

------------------------------------------------------------
-- * List-like utilities

reverse :: Seq a -> Seq a
reverse = Seq . reversef reverseN . unSeq

reversef :: (Node a -> Node a) -> FTree a -> FTree a
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
fromList = Seq . fromListBody . fmap Elem

fromListBody :: (Sized a) => [a] -> FTree a
fromListBody xs
  -- We use a lazy length-checking idiom here, but compute
  -- the length when we discover xs is short.
  | P.null ss = Simple (fromListN xs)
  | P.null (P.drop (2 * maxFringe - maxSimple) ss) =
    root (fromListN l) emptyTree (fromListN r)
  | otherwise = root lf d lr
  where b = P.length xs
        ss = P.drop maxSimple xs
        (l, r) = P.splitAt (b `quot` 2) xs
        (lf : ns) = nests xs
        View lr d = viewr' $ fromListBody ns

nests :: (Sized a) => [a] -> [Node a]
nests [] = []
nests xs =
  case P.splitAt maxInner xs of
    (nd, xs')
      | P.null xs' -> [fromListN nd]
      | P.null (P.drop (minInner-1) xs') ->
         case P.splitAt (P.length xs - minInner) xs of
           (l,r) -> [fromListN l, fromListN r]
      | otherwise -> fromListN nd : nests xs'

toList :: Seq a -> [a]
toList = foldr (:) []

------------------------------------------------------------
-- * Functor

instance Functor FTree where
  fmap f (Simple m) = Simple (fmap f m)
  fmap f (Root s l d r) =
    Root s (fmap f l) (fmap (fmap f) d) (fmap f r)
  -- a <$ s = replicate (size s) a

------------------------------------------------------------
-- * Pretty printing

-- This pretty printer is cheap and cheerful (eg not written in ShowS style)
pretty :: Show a => Seq a -> String
pretty = prettyf showN . unSeq

prettyr :: Show a => (a -> String) -> FTree a -> String
prettyr f t = "(" ++ prettyf (showNInner f) t ++ ")"

showN :: (Show a) => Node a -> String
showN (Node s n) = "<" ++ show s ++ ">" ++ show (N.toList n)

showNInner :: (a -> String) -> Node a -> String
showNInner f (Node n s) =
  "<" ++ show n ++ ">[" ++ P.drop 1 (N.foldr (\d r -> "," ++ f d ++ r) "" s) ++ "]"

prettyf :: Show a => (Node a -> String) -> FTree a -> String
prettyf f (Simple m) = "S " ++ f m
prettyf f (Root s l d r) = "R<" ++ show s ++ "> " ++ f l ++ " " ++ prettyr f d ++ " & " ++ f r

-- pretty print
pp :: Show a => Seq a -> IO ()
pp = putStrLn . pretty

------------------------------------------------------------
-- Invariant checker.  Passes through the value if OK, otherwise calls error.
naiveSizeof :: (a -> Size) -> (Node a -> Size)
naiveSizeof computeSize m = foldlN' (\a v -> a + computeSize v) 0 m

check :: (Show a) => Seq a -> Seq a
check (Seq a)
  | Just bug <- ok (const 1) showN a =
    error ("Violates invariant:\n" ++ bug ++ "\n\nData: " ++ show a)
  | otherwise = Seq a

-- OK is sort of the reverse of the usual Maybe monad; it either succeeds silently,
-- or fails with an error message.
ok :: (Show a) => (a -> Size) -> (Node a -> String) -> FTree a -> Maybe String
ok computeSize pr (Simple m) = okN computeSize pr 0 maxSimple m
ok computeSize pr n@(Root s l d r)
  | Just lerr <- okN computeSize pr minFringe maxFringe l = Just lerr
  | Just derr <- ok (naiveSizeof computeSize) (showNInner pr) d = Just derr
  | Just rerr <- okN computeSize pr minFringe maxFringe r = Just rerr
  | computedSize /= s =
    Just ("Computed size " ++ show computedSize ++ " different: " ++ prettyf pr n)
  | otherwise = Nothing
  where computedSize = size l + size d + size r

okN :: (a -> Size) -> (Node a -> String) -> Size -> Size -> Node a -> Maybe String
okN computeSize pr mn mx m
  | breadth m > mx = Just ("Node too big: " ++ pr m)
  | breadth m < mn = Just ("Node too small: " ++ pr m)
  | computedSize /= size m =
    Just ("Computed size " ++ show computedSize ++ " different: " ++ pr m)
  | otherwise = Nothing
  where computedSize = naiveSizeof computeSize m
