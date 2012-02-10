{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Data.VectorNode(
    Elem(..), Breadth(..), Size(..), Sized(..),
    Node, emptyN, singletonN,
    splitRNode, splitLNode, forceN, consN, snocN,
    breadth, headN, tailN, initN, lastN, appN, nullN,
    (!), foldlN', reverseN, fromListN, toListN, adjustN,
    takeN, dropN
    ) where
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import qualified Data.Vector as V

-- Breadth describes the width of a tree node.
type Breadth = Int

-- Size describes the count of items held in or beneath a node.
type Size = Int

data Node a = Node { nodeSize :: !Size, datum :: !(V.Vector a) }
  deriving (Eq, Functor, Foldable, Traversable)

------------------------------------------------------------
-- Size class.  Defined here because we need to specialize sizeN,
-- and use size while constructing nodes from nodes.

class Sized a where
  size :: a -> Size
  sizeN :: Node a -> Size
  sizeN (Node _ n) = V.foldl' (\s a -> s + size a) 0 n

-- For a while we weren't using Sized here, but were passing a size
-- function instead.  But local dictionary specialization ought to
-- apply if we use the type class, making that far more efficient
-- after inlining.
newtype Elem a = Elem { unElem :: a }
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show a => Show (Elem a) where
  showsPrec p (Elem e) = showsPrec p e  -- Don't show the wrappers.

instance Sized (Elem a) where
  size _ = 1
  sizeN (Node _ n) = V.length n

instance Sized (Node a) where
  size = nodeSize

------------------------------------------------------------
-- Node manipulation.

emptyN :: Node a
emptyN = Node 0 V.empty

singletonN :: Elem a -> Node (Elem a)
singletonN = Node 1 . V.singleton

-- Compute size of node the hard way, by summing element sizes.

{-# SPECIALIZE node :: V.Vector (Node a) -> Node (Node a) #-}
{-# SPECIALIZE node :: V.Vector (Elem a) -> Node (Elem a) #-}
node :: (Sized a) => V.Vector a -> Node a
node n = Node (sizeN r) n
  where r = Node (-1) n

-- Symmetric 0-copy split
splitNode :: V.Vector a -> Breadth -> (V.Vector a, V.Vector a)
splitNode n b = (V.take b n, V.drop b n)

-- Split for R, counting from left, copying left
{-# SPECIALIZE splitRNode :: Node (Node a) -> Breadth -> (Node (Node a), Node (Node a)) #-}
{-# SPECIALIZE splitRNode :: Node (Elem a) -> Breadth -> (Node (Elem a), Node (Elem a)) #-}
splitRNode :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitRNode (Node s n) b =
  case splitNode n b of
    (d, r) -> (node (V.force d), node r)

-- Split for L, counting from right, copying right
{-# SPECIALIZE splitLNode :: Node (Elem a) -> Breadth -> (Node (Elem a), Node (Elem a)) #-}
{-# SPECIALIZE splitLNode :: Node (Node a) -> Breadth -> (Node (Node a), Node (Node a)) #-}
splitLNode :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitLNode (Node s n) b =
  case splitNode n (V.length n - b) of
    (l, d) -> (node l, node (V.force d))

forceN :: Node a -> Node a
forceN (Node s n) = Node s (V.force n)

{-# SPECIALIZE consN :: (Elem a) -> Node (Elem a) -> Node (Elem a) #-}
{-# SPECIALIZE consN :: (Node a) -> Node (Node a) -> Node (Node a) #-}
consN :: (Sized a) => a -> Node a -> Node a
consN a (Node s n) = Node (size a + s) (V.cons a n)

{-# SPECIALIZE snocN :: Node (Elem a) -> (Elem a) -> Node (Elem a) #-}
{-# SPECIALIZE snocN :: Node (Node a) -> (Node a) -> Node (Node a) #-}
snocN :: (Sized a) => Node a -> a -> Node a
snocN (Node s n) a = Node (size a + s) (V.snoc n a)

breadth :: Node a -> Breadth
breadth (Node _ n) = V.length n

headN :: Node a -> a
headN (Node _ n) = V.head n

{-# SPECIALIZE tailN :: Node (Elem a) -> Node (Elem a)  #-}
{-# SPECIALIZE tailN :: Node (Node a) -> Node (Node  a)  #-}
tailN :: (Sized a) => Node a -> Node a
tailN (Node s n) = Node (s - size (V.head n)) (V.force (V.tail n))

lastN :: Node a -> a
lastN (Node _ n) = V.last n

{-# SPECIALIZE initN :: Node (Elem a) -> Node (Elem a)  #-}
{-# SPECIALIZE initN :: Node (Node a) -> Node (Node  a)  #-}
initN :: (Sized a) => Node a -> Node a
initN (Node s n) = Node (s - size (V.last n)) (V.force (V.init n))

appN :: Node a -> Node a -> Node a
appN (Node s1 n1) (Node s2 n2) = Node (s1+s2) (n1 V.++ n2)

nullN :: Node a -> Bool
nullN (Node s _) = s == 0

foldlN' :: (r -> a -> r) -> r -> Node a -> r
foldlN' f z (Node _ n) = V.foldl' f z n

reverseN :: Node a -> Node a
reverseN (Node s n) = Node s (V.reverse n)

{-# SPECIALIZE fromListN :: [Elem a] -> Node (Elem a)   #-}
{-# SPECIALIZE fromListN :: [Node a] -> Node (Node a)   #-}
fromListN :: (Sized a) => [a] -> Node a
fromListN xs = node (V.fromList xs)

toListN :: Node a -> [a]
toListN (Node _ v) = V.toList v

{-# INLINE adjustN #-}
-- Note that lack of Sized constraint forces this to be a
-- size-preserving adjustment.
adjustN :: (a -> a) -> Breadth -> Node a -> Node a
adjustN f i (Node s v) = Node s (v V.// [(i, f (v V.! i))])

{-# INLINE (!) #-}
(!) :: Node a -> Breadth -> a
(!) (Node s n) i = n V.! i

-- take without a Sized constraint (caller adjusts the size)
takeN :: Size -> Breadth -> Node a -> Node a
takeN s i (Node _ v) = Node s (V.take i v)

-- drop without a Sized constraint (caller adjusts the size)
dropN :: Size -> Breadth -> Node a -> Node a
dropN s i (Node _ v) = Node s (V.drop i v)