{- |
Module      :  Data.SemiIsoFunctor
Description :  Functors from the category of semi-isomoprihsms to Hask.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Defines a functor from the category of semi-isomoprihsms to Hask.

The most interesting property of that class is that it can be
instantiated by both covariant (like Parser) and contravariant (like Printer) 
functors. Therefore it can be used as a common interface to unify
parsing and pretty printing.

Operator names are up to bikeshedding :)
-}
module Data.SemiIsoFunctor where

import Control.Lens.Cons
import Control.Lens.Empty
import Control.Lens.SemiIso

infixl 3 /|/
infixl 4 /$/
infixl 5 /*/, /*, */

-- | A functor from the category of semi-isomorphisms to Hask.
--
-- It is both covariant and contravariant in its single arugment.
--
-- The contravariant map is used by default to provide compatibility with 
-- Prisms (otherwise you would have to reverse them in most cases).
--
-- Instances should satisfy laws:
-- 
-- > simap id      = id
-- > simap (f . g) = simap g . simap f
-- > simap         = simapCo . fromSemi
-- > simapCo       = simap   . fromSemi
class SemiIsoFunctor f where
    -- | The contravariant map.
    simap :: ASemiIso' a b -> f b -> f a
    simap = simapCo . fromSemi
    
    -- | The covariant map.
    simapCo :: ASemiIso' a b -> f a -> f b
    simapCo = simap . fromSemi
    
    {-# MINIMAL simap | simapCo #-}

-- | A infix operator for 'simap'.
(/$/) :: SemiIsoFunctor f => ASemiIso' a b -> f b -> f a
(/$/) = simap

-- | Equivalent of 'Applicative' for 'SemiIsoFunctor'.
--
-- However, this class implements uncurried application, unlike 
-- 'Control.Applicative' which gives you curried application.
--
-- Instances should satisfy laws:
-- 
-- > TODO (they should be fine)
class SemiIsoFunctor f => SemiIsoApply f where
    sipure :: ASemiIso' a () -> f a
    (/*/) :: f a -> f b -> f (a, b)

    (/*)  :: f a -> f () -> f a
    f /* g = unit /$/ f /*/ g

    (*/)  :: f () -> f b -> f b
    f */ g = unit . swapped /$/ f /*/ g

    {-# MINIMAL sipure, (/*/) #-}

-- | Equivalent of 'Alternative' for 'SemiIsoFunctor'.
--
-- @f a@ should form a monoid with identity 'siempty' and binary
-- operation '/|/'.
class SemiIsoApply f => SemiIsoAlternative f where
    siempty :: f a
    (/|/) :: f a -> f a -> f a

    sisome :: f a -> f [a]
    sisome v = _Cons /$/ v /*/ simany v

    simany :: f a -> f [a]
    simany v = sisome v /|/ sipure _Empty

    {-# MINIMAL siempty, (/|/) #-}

-- | Equivalent of 'sequence'.
--
-- Note that it is not possible to write sequence_, because
-- you cannot void a SemiIsoFunctor.
sisequence :: SemiIsoApply f => [f a] -> f [a]
sisequence [] = sipure _Empty
sisequence (x:xs) = _Cons /$/ x /*/ sisequence xs

-- | Equivalent of 'replicateM'.
sireplicate :: SemiIsoApply f => Int -> f a -> f [a]
sireplicate n f = sisequence (replicate n f)
