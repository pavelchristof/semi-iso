{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Control.Category.Inclusion (
    Inclusion,
    AnInclusion,
    Concrete(..),
    (<:)(..),
    CatTrans(..)
    ) where

import Control.Category
import Data.Semigroupoid.Dual
import Prelude hiding (id, (.))
import Unsafe.Coerce

data A
data B

-- | An inclusion from a subcategory @sub@ to category @cat@.
type Inclusion sub cat = forall a b. sub a b -> cat a b

-- | Monomorphic equivalent of 'Inclusion', using a trick.
type AnInclusion sub cat = sub A B -> cat A B

-- | A concrete category, representable in Hask.
class Category cat => Concrete (cat :: k -> k -> *) where
    type Repr (cat :: k -> k -> *) (a :: k) (b :: k)
    repr :: cat a b -> Repr cat a b
    inst :: Repr cat a b -> cat a b

instance Concrete cat => Concrete (Dual cat) where
    type Repr (Dual cat) a b = Repr cat b a
    repr = repr . getDual
    inst = getDual . inst

newtype (sub :: * -> * -> *) <: (cat :: * -> * -> *) = Sub { runEmbed :: Inclusion sub cat }

instance Category (<:) where
    id = Sub id
    Sub f . Sub g = Sub (f . g)

instance Concrete (<:) where
    type Repr (<:) (sub :: * -> * -> *) (cat :: * -> * -> *) = AnInclusion sub cat
    repr = runEmbed
    inst = Sub . unsafeCoerce

-- | A category transformer.
class CatTrans t where
    -- | Lift an arrow from the base category.
    clift :: Category cat => Inclusion cat (t cat)
