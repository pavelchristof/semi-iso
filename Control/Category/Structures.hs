{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{- |
Module      :  Control.Category.Structures
Description :  Structures in a category.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

This module defines some basic structures in a category in a more fine-grained
way then "Control.Arrow".

Unfortunately names in this module clash with "Control.Arrow".
-}
module Control.Category.Structures where

import           Control.Arrow (Kleisli(..))
import qualified Control.Arrow as BadArrow
import           Control.Category
import           Control.Category.Inclusion
import           Control.Monad
import           Data.Semigroupoid.Dual
import           Prelude hiding (id, (.))

infixr 1 ^>>, ^<<, #>>, #<<
infixr 1 >>^, <<^, >>#, <<#
infixl 3 ***
infixl 2 +++
infixl 3 /+/

-- | A category with finite products.
class Category cat => Products cat where
    -- | Send the first component of the input through the argument arrow, and copy the rest unchanged to the output.
    --
    -- @first a@ is equal to @a *** id@.
    first :: cat a b -> cat (a, c) (b, c)
    first a = a *** id

    -- | A mirror image of 'first'.
    --
    -- @second a@ is equal to @id *** a@.
    second :: cat a b -> cat (c, a) (c, b)
    second a = id *** a

    -- | A product of two arrows.
    -- Split the input between the two argument arrows and combine their output.
    (***) :: cat a b -> cat c d -> cat (a, c) (b, d)
    a *** b = first a >>> second b

    {-# MINIMAL (***) | first, second #-}

instance Monad m => Products (Kleisli m) where
    (***) = (BadArrow.***)

instance Products cat => Products (Dual cat) where
    Dual f *** Dual g = Dual $ second g >>> first f

instance Products (->) where
    (***) = (BadArrow.***)

-- | A category with finite coproducts.
class Category cat => Coproducts cat where
    -- | Feed marked inputs through the argument arrow, passing the rest through unchanged to the output.
    --
    -- @left a@ is equal to @a +++ id@.
    left :: cat a b -> cat (Either a c) (Either b c)
    left a = a +++ id

    -- | A mirror image of left.
    --
    -- @right a@ is equal to @id +++ a@.
    right :: cat a b -> cat (Either c a) (Either c b)
    right a = id +++ a

    -- | A coproduct of two arrows.
    -- Split the input between the two argument arrows, retagging and merging their outputs.
    (+++) :: cat a b -> cat c d -> cat (Either a c) (Either b d)
    a +++ b = left a >>> right b

    {-# MINIMAL (+++) | left, right #-}

instance Monad m => Coproducts (Kleisli m) where
    (+++) = (BadArrow.+++)

instance Coproducts cat => Coproducts (Dual cat) where
    Dual f +++ Dual g = Dual $ right g >>> left f

instance Coproducts (->) where
    (+++) = (BadArrow.+++)

-- | A category @cat@ is a CatPlus when @cat a b@ is a monoid for all a, b.
class Category cat => CatPlus cat where
    -- | The identity of '/+/'.
    cempty :: cat a b
    -- | An associative operation on arrows.
    (/+/) :: cat a b -> cat a b -> cat a b

    {-# MINIMAL cempty, (/+/) #-}

instance MonadPlus m => CatPlus (Kleisli m) where
    cempty = BadArrow.zeroArrow
    (/+/)  = (BadArrow.<+>)

instance CatPlus cat => CatPlus (Dual cat) where
    cempty = Dual cempty
    Dual f /+/ Dual g = Dual $ f /+/ g

class Category cat => Dagger cat where
    dagger :: cat a b -> cat b a

-- | An arrow is a category that embeds some concrete category.
class (Concrete (Base cat), Category cat) => Arrow cat where
    type Base cat :: * -> * -> *
    arr :: Inclusion (Repr (Base cat)) cat

instance Arrow cat => Arrow (Dual cat) where
    type Base (Dual cat) = Dual (Base cat)
    arr = Dual . arr

rarr :: (Arrow cat, Dagger cat) => Repr (Base cat) a b -> cat b a
rarr = dagger . arr

-- | Composes a function with an arrow.
(^>>) :: Arrow cat => Repr (Base cat) a b -> cat b c -> cat a c
f ^>> a = arr f >>> a

-- | Composes an arrow with a function.
(>>^) :: Arrow cat => cat a b -> Repr (Base cat) b c -> cat a c
a >>^ f = a >>> arr f

-- | Composes a function with an arrow, backwards.
(^<<) :: Arrow cat => Repr (Base cat) b c -> cat a b -> cat a c
f ^<< a = arr f <<< a

-- | Composes an arrow with a function, backwards.
(<<^) :: Arrow cat => cat b c -> Repr (Base cat) a b -> cat a c
a <<^ f = a <<< arr f

-- | Composes the dagger (inverse) of a function with an arrow.
(#>>) :: (Arrow cat, Dagger cat) => Repr (Base cat) b a -> cat b c -> cat a c
f #>> a = rarr f >>> a

-- | Composes an arrow with the dagger (inverse) of a function.
(>>#) :: (Arrow cat, Dagger cat) => cat a b -> Repr (Base cat) c b -> cat a c
a >># f = a >>> rarr f

-- | Composes the dagger (inverse) of a function with an arrow, backwards.
(#<<) :: (Arrow cat, Dagger cat) => Repr (Base cat) c b -> cat a b -> cat a c
f #<< a = rarr f <<< a

-- | Composes an arrow with the dagger (inverse) of a function, backwards.
(<<#) :: (Arrow cat, Dagger cat) => cat b c -> Repr (Base cat) b a -> cat a c
a <<# f = a <<< rarr f
