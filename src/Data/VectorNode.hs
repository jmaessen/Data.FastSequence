{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Data.VectorNode(
    Elem(..), Breadth, Size, Sized(..),
    Node, empty, singleton,
    splitR, splitL, force, cons, snoc,
    breadth, head, tail, init, last, append, null,
    (!), foldl', reverse, fromList, toList, adjust,
    take, drop, replicate
    ) where
import Prelude hiding (head, tail, init, last, take, drop, null, reverse, replicate)
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable(..))
import qualified Data.Vector as V

-- Breadth describes the width of a tree node.
type Breadth = Int

-- Size describes the count of items held in or beneath a node.
type Size = Int

data Node a = Node {-# UNPACK #-} !Size {-# UNPACK #-} !(V.Vector a)
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
  size (Node s _) = s

------------------------------------------------------------
-- Node manipulation.

empty :: Node a
empty = Node 0 V.empty

singleton :: Elem a -> Node (Elem a)
singleton = Node 1 . V.singleton

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
{-# SPECIALIZE splitR :: Node (Node a) -> Breadth -> (Node (Node a), Node (Node a)) #-}
{-# SPECIALIZE splitR :: Node (Elem a) -> Breadth -> (Node (Elem a), Node (Elem a)) #-}
splitR :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitR (Node s n) b =
  case splitNode n b of
    (d, r) -> (node (V.force d), node r)

-- Split for L, counting from right, copying right
{-# SPECIALIZE splitL :: Node (Elem a) -> Breadth -> (Node (Elem a), Node (Elem a)) #-}
{-# SPECIALIZE splitL :: Node (Node a) -> Breadth -> (Node (Node a), Node (Node a)) #-}
splitL :: (Sized a) => Node a -> Breadth -> (Node a, Node a)
splitL (Node s n) b =
  case splitNode n (V.length n - b) of
    (l, d) -> (node l, node (V.force d))

force :: Node a -> Node a
force (Node s n) = Node s (V.force n)

{-# SPECIALIZE cons :: (Elem a) -> Node (Elem a) -> Node (Elem a) #-}
{-# SPECIALIZE cons :: (Node a) -> Node (Node a) -> Node (Node a) #-}
cons :: (Sized a) => a -> Node a -> Node a
cons a (Node s n) = Node (size a + s) (V.cons a n)

{-# SPECIALIZE snoc :: Node (Elem a) -> (Elem a) -> Node (Elem a) #-}
{-# SPECIALIZE snoc :: Node (Node a) -> (Node a) -> Node (Node a) #-}
snoc :: (Sized a) => Node a -> a -> Node a
snoc (Node s n) a = Node (size a + s) (V.snoc n a)

breadth :: Node a -> Breadth
breadth (Node _ n) = V.length n

head :: Node a -> a
head (Node _ n) = V.head n

{-# SPECIALIZE tail :: Node (Elem a) -> Node (Elem a)  #-}
{-# SPECIALIZE tail :: Node (Node a) -> Node (Node  a)  #-}
tail :: (Sized a) => Node a -> Node a
tail (Node s n) = Node (s - size (V.head n)) (V.force (V.tail n))

last :: Node a -> a
last (Node _ n) = V.last n

{-# SPECIALIZE init :: Node (Elem a) -> Node (Elem a)  #-}
{-# SPECIALIZE init :: Node (Node a) -> Node (Node  a)  #-}
init :: (Sized a) => Node a -> Node a
init (Node s n) = Node (s - size (V.last n)) (V.force (V.init n))

append :: Node a -> Node a -> Node a
append (Node s1 n1) (Node s2 n2) = Node (s1+s2) (n1 V.++ n2)

null :: Node a -> Bool
null (Node s _) = s == 0

foldl' :: (r -> a -> r) -> r -> Node a -> r
foldl' f z (Node _ n) = V.foldl' f z n

reverse :: Node a -> Node a
reverse (Node s n) = Node s (V.reverse n)

{-# SPECIALIZE fromList :: [Elem a] -> Node (Elem a)   #-}
{-# SPECIALIZE fromList :: [Node a] -> Node (Node a)   #-}
fromList :: (Sized a) => [a] -> Node a
fromList xs = node (V.fromList xs)

toList :: Node a -> [a]
toList (Node _ v) = V.toList v

{-# INLINE adjust #-}
-- Note that lack of Sized constraint forces this to be a
-- size-preserving adjustment.
adjust :: (a -> a) -> Breadth -> Node a -> Node a
adjust f i (Node s v) = Node s (v V.// [(i, f (v V.! i))])

{-# INLINE (!) #-}
(!) :: Node a -> Breadth -> a
(!) (Node s n) i = n V.! i

-- take without a Sized constraint (caller adjusts the size)
take :: Size -> Breadth -> Node a -> Node a
take s i (Node _ v) = Node s (V.take i v)

-- drop without a Sized constraint (caller adjusts the size)
drop :: Size -> Breadth -> Node a -> Node a
drop s i (Node _ v) = Node s (V.drop i v)

-- replication
replicate :: Size -> Breadth -> a -> Node a
replicate s i a = Node s (V.replicate i a)
