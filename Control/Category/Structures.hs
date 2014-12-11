{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{- |
Module      :  Control.Category.Structures
Description :  Structures in a category.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

-}
module Control.Category.Structures where

import           Control.Arrow (Kleisli(..))
import qualified Control.Arrow as BadArrow
import           Control.Category
import           Control.Monad
import           Prelude hiding (id, (.))

infixl 3 ***
infixl 2 +++
infixl 3 /+/

class Category cat => Products cat where
    first :: cat a b -> cat (a, c) (b, c)
    first a = a *** id

    second :: cat a b -> cat (c, a) (c, b)
    second a = id *** a

    (***) :: cat a b -> cat c d -> cat (a, c) (b, d)
    a *** b = first a >>> second b

    {-# MINIMAL (***) | first, second #-}

instance Monad m => Products (Kleisli m) where
    (***) = (BadArrow.***)

class Category cat => Coproducts cat where
    left :: cat a b -> cat (Either a c) (Either b c)
    left a = a +++ id

    right :: cat a b -> cat (Either c a) (Either c b)
    right a = id +++ a

    (+++) :: cat a b -> cat c d -> cat (Either a c) (Either b d)
    a +++ b = left a >>> right b

    {-# MINIMAL (+++) | left, right #-}

instance Monad m => Coproducts (Kleisli m) where
    (+++) = (BadArrow.+++)

class Category cat => CatPlus cat where
    cempty :: cat a b
    (/+/) :: cat a b -> cat a b -> cat a b

    {-# MINIMAL cempty, (/+/) #-}

instance MonadPlus m => CatPlus (Kleisli m) where
    cempty = BadArrow.zeroArrow
    (/+/)  = (BadArrow.<+>)

class CategoryTrans t where
    clift :: Category cat => cat a b -> t cat a b

    {-# MINIMAL clift #-}
