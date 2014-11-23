{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
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
-}
module Data.SemiIsoFunctor where

import Control.Lens.Cons
import Control.Lens.Empty
import Control.Lens.Internal.SemiIso
import Control.Lens.SemiIso
import Data.Functor.Identity
import Data.Tuple.Morph

infixl 3 /|/
infixl 4 /$/, ~$/, /$~, ~$~
infixl 5 /*/, /*, */
infixl 1 //=
infixr 1 =//

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
    simap = simapCo . rev

    -- | The covariant map.
    simapCo :: ASemiIso' a b -> f a -> f b
    simapCo = simap . rev

    {-# MINIMAL simap | simapCo #-}

-- | A infix operator for 'simap'.
(/$/) :: SemiIsoFunctor f => ASemiIso' a b -> f b -> f a
(/$/) = simap

-- | @ai /$~ f@ is equal to @ai . morphed /$/ f@.
--
-- This operator handles all the hairy stuff with uncurried application:
-- it reassociates the argument tuple and removes unnecessary (or adds necessary)
-- units to match the function type. You don't have to use /* and */ with this
-- operator.
(/$~) :: (SemiIsoFunctor f, HFoldable b', HFoldable b,
          HUnfoldable b', HUnfoldable b, Rep b' ~ Rep b)
      => ASemiIso' a b' -> f b -> f a
(SemiIso f g) /$~ h = semiIso f g . morphed /$/ h

-- | @ai ~$/ f@ is equal to @morphed . ai /$/ f@.
(~$/) :: (SemiIsoFunctor f, HFoldable a', HFoldable a,
          HUnfoldable a', HUnfoldable a, Rep a' ~ Rep a)
      => ASemiIso' a' b -> f b -> f a
(SemiIso f g) ~$/ h = morphed . semiIso f g /$/ h

-- | @ai ~$~ f@ is equal to @morphed . ai . morphed /$/ f@.
(~$~) :: (SemiIsoFunctor f, HFoldable b', HFoldable b', HFoldable b,
          HFoldable a, HUnfoldable b', HUnfoldable b', HUnfoldable b,
          HUnfoldable a, Rep b' ~ Rep b, Rep b' ~ Rep a)
      => ASemiIso b' b' b' b' -> f b -> f a
(SemiIso f g) ~$~ h = morphed . semiIso f g . morphed /$/ h

-- | Equivalent of 'Applicative' for 'SemiIsoFunctor'.
--
-- However, this class implements uncurried application, unlike 
-- 'Control.Applicative' which gives you curried application.
--
-- Instances should satisfy laws:
-- 
-- > TODO (they should be fine)
class SemiIsoFunctor f => SemiIsoApply f where
    siunit :: f ()
    siunit = sipure id

    sipure :: ASemiIso' a () -> f a
    sipure ai = ai /$/ siunit

    sipureCo :: ASemiIso' () a -> f a
    sipureCo ai = ai `simapCo` siunit

    (/*/) :: f a -> f b -> f (a, b)

    (/*)  :: f a -> f () -> f a
    f /* g = unit /$/ f /*/ g

    (*/)  :: f () -> f b -> f b
    f */ g = unit . swapped /$/ f /*/ g

    {-# MINIMAL (siunit | sipure), (/*/) #-}

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

class SemiIsoApply m => SemiIsoMonad m where
    (//=) :: m a -> (a -> m b) -> m (a, b)
    m //= f = swapped /$/ (f =// m)

    (=//) :: (b -> m a) -> m b -> m (a, b)
    f =// m = swapped /$/ (m //= f)

class SemiIsoMonad m => SemiIsoFix m where
    sifix :: (a -> m a) -> m a
    sifix f = dup /$/ (f =//= f)
      where dup = semiIso (\a -> Right (a, a)) (Right . fst)

    (=//=) :: (a -> m b) -> (b -> m a) -> m (a, b)
    f =//= g = sifix (\(a, b) -> g b /*/ f a)

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
