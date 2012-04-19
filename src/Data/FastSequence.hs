{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Data.FastSequence(
    empty, singleton, (|>), (<|), fromList, toList, null, length,
    head, tail, init, last, ViewL(..), viewl, ViewR(..), viewr,
    reverse, tails, inits, (><),
    index, adjust, update, take, drop, splitAt,
    replicate, -- replicateA, replicateM
    pretty, pp, check
    ) where
import Prelude hiding ( null, reverse, length, head, tail,
                        init, last, take, drop, splitAt, foldr,
                        replicate )
import qualified Prelude as P
import Data.List(foldl')
import Data.Foldable(Foldable(..), toList)
import Data.Traversable(Traversable(..))
import Data.Typeable(Typeable1(..))
import Data.VectorNode(Size(..), Breadth(..), Elem(..), Sized(..), Node, (!))
import qualified Data.VectorNode as N

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

newtype Seq a = Seq { unSeq :: FTree (Elem a) }
  deriving (Functor, Foldable, Traversable)

instance (Show a) => Show (Seq a) where
  showsPrec p (Seq s) = showsPrec p s  -- Temporary, for debugging.

instance (Show a) => Show (Node a) where
  show = showN

data FTree a =
    Simple {-# UNPACK #-} !(Node a)
  | Root {-# UNPACK #-} !Size {-# UNPACK #-} !(Node a) (FTree (Node a)) {-# UNPACK #-} !(Node a)
  deriving (Foldable, Traversable)

instance (Show a) => Show (FTree a) where
  show = prettyf showN

------------------------------------------------------------
-- * Sized objects

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
emptyTree = Simple N.empty

empty :: Seq a
empty = Seq emptyTree

singleton :: a -> Seq a
singleton = Seq . Simple . N.singleton . Elem

(<|) :: a -> Seq a -> Seq a
a <| Seq sq = Seq (cons (Elem a) sq)

cons :: (Sized a) => a -> FTree a -> FTree a
cons a (Simple m)
  | N.breadth m < maxSimple = Simple (N.cons a m)
  | otherwise =
    case N.splitL m maxInner of
      (l, r) -> Root (size a + size m) (N.cons a l) emptyTree r
cons a (Root s l d r)
  | N.breadth l < maxFringe = Root (size a + s) (N.cons a l) d r
  | otherwise =
    case N.splitL l maxInner of
      (l', d') -> Root (size a + s) (N.cons a l') (cons d' d) r

(|>) :: Seq a -> a -> Seq a
Seq sq |> a = Seq (snoc sq (Elem a))

snoc :: (Sized a) => FTree a -> a -> FTree a
snoc (Simple m) b
  | N.breadth m < maxSimple = Simple (N.snoc m b)
  | otherwise =
    case N.splitR m maxInner of
      (l, r) -> Root (size b + size m) l emptyTree (N.snoc r b)
snoc (Root s l d r) b
  | N.breadth r < maxFringe = Root (size b + s) l d (N.snoc r b)
  | otherwise =
    case N.splitR r maxInner of
      (d', r') -> Root (size b + s) l (snoc d d') (N.snoc r' b)

(><) :: Seq a -> Seq a -> Seq a
Seq sq1 >< Seq sq2 = Seq (append sq1 sq2)

append :: (Sized a) => FTree a -> FTree a -> FTree a
append (Simple m1) (Simple m2)
  | N.breadth m1 == 0 = Simple m2
  | N.breadth m2 == 0 = Simple m1
  | otherwise = simple (N.append m1 m2)
append (Simple m) (Root s l d r)
  | N.breadth m == 0 = Root s l d r
  | otherwise = midL (s + size m) (N.append m l) d r
append (Root s l d r) (Simple m)
  | N.breadth m == 0 = Root s l d r
  | otherwise = midR (s + size m) l d (N.append r m)
append (Root sl ll dl rl) (Root sr lr dr rr) =
  Root (sl + sr) ll (append dl (mid (N.append rl lr) dr)) rr

-- midL builds a root from a too-big left Node a, where the root has a left
-- Node a of size at most maxFringe
midL :: (Sized a) => Size -> Node a -> FTree (Node a) -> Node a -> FTree a
midL s l d r
  | b <= maxFringe = Root s (N.force l) d r
  | otherwise =
    case N.splitL l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> midL s ll (cons lr d) r
  where b = N.breadth l

-- mid is midL that pushes everything into "d"
mid :: (Sized a) => Node a -> FTree (Node a) -> FTree (Node a)
mid l d
  | b <= maxInner = cons (N.force l) d
  | otherwise =
    case N.splitL l (((b + 1) `quot` 2) `min` maxInner) of
      (ll, lr) -> mid ll (cons lr d)
  where b = N.breadth l

-- midR pastes FTree (Node a) onto a too-big (Node a)
midR :: (Sized a) => Size -> Node a -> FTree (Node a) -> Node a -> FTree a
midR s l d r
  | b <= maxFringe = Root s l d (N.force r)
  | otherwise =
    case N.splitR r (((b+1) `quot` 2) `min` maxInner) of
      (rl, rr) -> midR s l (snoc d rl) rr
  where b = N.breadth r

-- A meta-constructor for possibly-too-big Nodes
simple :: (Sized a) => Node a -> FTree a
simple m
  | b <= maxSimple = Simple m
  | otherwise =
    case N.splitR m (((b+1) `quot` 2) `min` maxInner) of
      (l, r) -> midR (size m) l emptyTree r
  where b = N.breadth m

null :: Seq a -> Bool
null (Seq (Simple m)) = N.null m
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
  | N.null m = Empty
  | otherwise = View (N.head m) (Simple (N.tail m))
viewl' (Root s l d r) = View hn (rootL (s - size hn) (N.tail l) d r)
  where hn = N.head l

-- Create a Root node with a potentially undersized l
rootL :: Size -> Node a -> FTree (Node a) -> Node a -> FTree a
rootL s l d r
  | N.breadth l >= minFringe = Root s l d r
  | otherwise =
    case viewl' d of
      View l' d' -> Root s (N.append l l') d' r
      Empty      -> Simple (N.append l r)

head :: Seq a -> a
head (Seq (Simple m))
  | N.null m   = error "head empty"
  | otherwise = unElem (N.head m)
head (Seq (Root s l d r)) = unElem (N.head l)

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
  | N.null m = Empty
  | otherwise = View (N.last m) (Simple (N.init m))
viewr' (Root s l d r) = View ln (rootR (s - size ln) l d (N.init r))
  where ln = N.last r

-- Create a Root node with a potentially undersized R
rootR :: Size -> Node a -> FTree (Node a) -> Node a -> FTree a
rootR s l d r
  | N.breadth r >= minFringe = Root s l d r
  | otherwise =
    case viewr' d of
      View r' d' -> Root s l d' (N.append r' r)
      Empty      -> Simple (N.append l r)

init :: Seq a -> Seq a
init t =
  case viewr t of
    EmptyR -> error "init empty"
    r :> _ -> r

last :: Seq a -> a
last (Seq (Simple m))
  | N.null m   = error "last empty"
  | otherwise = unElem (N.last m)
last (Seq (Root s l d r)) = unElem (N.last r)

------------------------------------------------------------
-- * Indexing and indexed operations

index :: (Show a) => Seq a -> Size -> a
index !m i | i < 0 = indexErr
index (Seq (Simple m)) i | i < size m = unElem (m ! i)
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
indexN i !n = loop 0 i
  where loop position i
          | i < se = (i, e)
          | otherwise = loop (position + 1) (i - se)
          where e = n ! position
                se = size e

adjust :: (a -> a) -> Size -> Seq a -> Seq a
adjust f i !m | i < 0 = adjustErr
adjust f i (Seq (Simple m))
  | i < size m = Seq (Simple (N.adjust (Elem . f . unElem) i m))
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
adjustN' f i0 !n = loop 0 i0
  where loop position i
          | i < se = N.adjust (f i) position n
          | otherwise = loop (position + 1) (i - se)
          where e = n ! position
                se = size e

update :: Size -> a -> Seq a -> Seq a
update i v !m | i < 0 || i >= length m = updateErr
update i v m = adjust (const v) i m

updateErr :: a
updateErr = error "FastSequence.update: index out of bounds"

------------------------------------------------------------
-- * Take, drop, and splitAt
-- These have similar recursive structure.  We choose to implement them
-- by returning nested sequence upwards, rather than passing down a
-- a continuation (so, more like index rather than adjust/update).

take :: Size -> Seq a -> Seq a
take i !sq | i <= 0 = empty
take i sq@(Seq (Simple n))
  | i < s = Seq (Simple (N.take i i n))
  where s = size n
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
takeN' i0 !n = loop 0 i0
  where loop position i
          | i < se = (i, N.take (i0 - i) position n, e)
          | otherwise = loop (position + 1) (i - se)
          where e = n ! position
                se = size e

drop :: Size -> Seq a -> Seq a
drop i sq | i <= 0 = sq
drop i sq@(Seq (Simple n))
  | i < s = Seq (Simple (N.drop (s - i) i n))
  where s = size n
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
dropN' i0 !n = loop 0 i0
  where loop position i
          | i < se = (i, N.drop (s - i0 + i - se) (position + 1) n, e)
          | otherwise = loop (position + 1) (i - se)
          where e = n ! position
                se = size e
                s = size n

-- splitAt is non-strict in its pair result, but both elements
-- are argument-strict.
splitAt :: Size -> Seq a -> (Seq a, Seq a)
splitAt i sq = (a, b)
  where (a, b) = splitAt0 i sq

-- splitAt0 is strict
splitAt0 :: Size -> Seq a -> (Seq a, Seq a)
splitAt0 i !sq | i <= 0 = (empty, sq)
splitAt0 i sq@(Seq (Simple n))
  | i < s = (Seq (Simple (N.take i i n)),
             Seq (Simple (N.drop (s - i) i n)))
  where s = size n
splitAt0 i sq@(Seq t@(Root s l d r))
  | i < s =
    case splitAt' i t of
      (_, r, m, l) -> (Seq r, Seq (cons m l))
splitAt0 i sq = (sq, empty)

-- Result is (remaining elements to split, head without those elements,
-- middle element from which elements may possibly be split,
-- tail without those elements).
splitAt' :: (Sized a) => Size -> FTree a -> (Size, FTree a, a, FTree a)
splitAt' i (Simple m) =
  case splitAtN' i m of
    (i', r, m, l) -> (i', Simple r, m, Simple l)
splitAt' i (Root s l d r)
  | i < sl =
    case splitAtN' i l of
      (i', r', m, l') -> (i', Simple r', m, rootL (s - i + i' - size m) l' d r)
  | i < sld =
    case splitAt' (i - sl) d of
      (i1, dl, m1, dr) ->
        case splitAtN' i1 m1 of
          (i2, r2, m2, l2) ->
            (i2, rootR (i - i2) l dl r2, m2, rootL (s - (i - i2) - size m2) l2 dr r)
  | otherwise =
    case splitAtN' (i - sld) r of
      (i', r', m, l') -> (i', rootR (i - i') l d r', m, Simple l')
  where sl = size l
        sld = sl + size d

splitAtN' :: Sized a => Size -> Node a -> (Size, Node a, a, Node a)
splitAtN' i0 !n = loop 0 i0
  where loop position i
          | i < se = (i, N.take (i0 - i) position n, e,
                         N.drop (s - (i0 - i) - se) (position + 1) n)
          | otherwise = loop (position + 1) (i - se)
          where e = n ! position
                se = size e
                s = size n

------------------------------------------------------------
-- * List-like utilities

reverse :: Seq a -> Seq a
reverse = Seq . reversef N.reverse . unSeq

reversef :: (Node a -> Node a) -> FTree a -> FTree a
reversef f (Simple m) = Simple (f m)
reversef f (Root s l d r) = Root s (f r) (reversef f' d) (f l)
  where f' = fmap f . N.reverse

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
  | P.null ss = Simple (N.fromList xs)
  | P.null (P.drop (2 * maxFringe - maxSimple) ss) =
    root (N.fromList l) emptyTree (N.fromList r)
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
      | P.null xs' -> [N.fromList nd]
      | P.null (P.drop (minInner-1) xs') ->
         case P.splitAt (P.length xs - minInner) xs of
           (l,r) -> [N.fromList l, N.fromList r]
      | otherwise -> N.fromList nd : nests xs'

------------------------------------------------------------
-- * Replication, with and without effects.

replicate :: Size -> a -> Seq a
replicate n a = Seq $ replicate' n 1 (Elem a)

replicate' :: (Sized a) => Size -> Size -> a -> FTree a
replicate' n size_t t
  | n <= maxSimple = Simple (N.replicate sz n t)
  | even sides = Root sz left mid left
  | otherwise = Root sz left mid right
  where sz = n * size_t
        (q,r) = n `quotRem` maxInner
        deepSize = maxInner * size_t
        deep = N.replicate deepSize maxInner t
        sides = r + 2 * maxInner
        half = sides `quot` 2
        rest = sides - half
        left = N.replicate (half * size_t) half t
        right = N.replicate (rest * size_t) rest t
        mid = replicate' (q-2) deepSize deep

-- TODO: replicateA and replicateM

------------------------------------------------------------
-- * Iterative construction

-- Do this in terms of list for now, as batched creation is well
-- handled in fromList and handed creation seems like it won't gain --
-- much -- from writing out longhand.

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
showN n = "<" ++ show (size n) ++ ">" ++ show (N.toList n)

showNInner :: (a -> String) -> Node a -> String
showNInner f n =
  "<" ++ show (size n) ++ ">[" ++
  P.drop 1 (P.foldr (\d r -> "," ++ f d ++ r) "" (N.toList n)) ++ "]"

prettyf :: Show a => (Node a -> String) -> FTree a -> String
prettyf f (Simple m) = "S " ++ f m
prettyf f (Root s l d r) = "R<" ++ show s ++ "> " ++ f l ++ " " ++ prettyr f d ++ " & " ++ f r

-- pretty print
pp :: Show a => Seq a -> IO ()
pp = putStrLn . pretty

------------------------------------------------------------
-- Invariant checker.  Passes through the value if OK, otherwise calls error.
naiveSizeof :: (a -> Size) -> (Node a -> Size)
naiveSizeof computeSize m = N.foldl' (\a v -> a + computeSize v) 0 m

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
  | N.breadth m > mx = Just ("Node too big: " ++ pr m)
  | N.breadth m < mn = Just ("Node too small: " ++ pr m)
  | computedSize /= size m =
    Just ("Computed size " ++ show computedSize ++ " different: " ++ pr m)
  | otherwise = Nothing
  where computedSize = naiveSizeof computeSize m
