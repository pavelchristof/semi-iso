{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      :  Control.SIArrow
Description :  Categories of reversible computations.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Categories of reversible computations.
-}
module Control.SIArrow (
    -- * Arrow.
    SIArrow,
    SIBind(..),
    (^>>), (>>^), (^<<), (<<^),
    (#>>), (>>#), (#<<), (<<#),

    -- * Functor and applicative.
    (/$/), (/$~),
    (/*/), (/*), (*/),

    -- * Signaling errors.
    sifail, (/?/),

    -- * Combinators.
    simany,
    sisome,
    sisequence,
    sisequence_,
    sireplicate,
    sireplicate_
    ) where

import Control.Category
import Control.Category.Structures
import Control.Lens.Cons
import Control.Lens.Empty
import Control.Lens.Iso
import Control.Lens.SemiIso
import Control.Monad
import Data.Tuple.Morph
import Prelude hiding (id, (.))

infixl 4 /$/, /$~
infixl 5 /*/, */, /*
infixl 3 /?/

-- | An SIArrow is a category of partial reversible computations.
type SIArrow cat = ( Category cat
                   , Products cat
                   , Coproducts cat
                   , Dagger cat
                   , GArrow cat
                   , Base cat ~ (<~>)
                   )

-- | SIArrows that admit a bind-like operation.
class SIArrow cat => SIBind cat where
    -- | Allows a computation to depend on a its input value.
    --
    -- I am not sure if this is the right way to get that ArrowApply or Monad
    -- like power. It seems quite easy to break the parser/pretty-printer inverse
    -- guarantee using this. On the other hand we have to be careful only when
    -- constructing the SemiIso using 'iso'/'semiIso' - and with an invalid SemiIso
    -- we could break everything anyway using 'siarr'.
    sibind :: ASemiIso a (cat a b) (cat a b) b -> cat a b

--instance SIBind cat => SIBind (Dual cat) where
--    sibind ai = Dual $ sibind (iso id getDual . rev ai . iso getDual id)

instance SIBind (<~>) where
    sibind ai = ReifiedSemiIso' $
        semiIso (\a -> apply ai a >>= flip apply a . runSemiIso)
                (\b -> unapply ai b >>= flip unapply b . runSemiIso)

-- | Postcomposes an arrow with a reversed SemiIso.
-- The analogue of '<$>' and synonym for '#<<'.
(/$/) :: SIArrow cat => ASemiIso' b' b -> cat a b -> cat a b'
(/$/) = (#<<)

-- | Convenient fmap.
--
-- > ai /$~ f = ai . morphed /$/ f
--
-- This operator handles all the hairy stuff with uncurried application:
-- it reassociates the argument tuple and removes unnecessary (or adds necessary)
-- units to match the function type. You don't have to use @/*@ and @*/@ with this
-- operator.
(/$~) :: (SIArrow cat, HFoldable b', HFoldable b,
           HUnfoldable b', HUnfoldable b, Rep b' ~ Rep b)
       => ASemiIso' a b' -> cat c b -> cat c a
ai /$~ h = cloneSemiIso ai . morphed /$/ h

-- | The product of two arrows with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '<*>'.
(/*/) :: SIArrow cat => cat () b -> cat () c -> cat () (b, c)
a /*/ b = unit ^>> (a *** b)

-- | The product of two arrows, where the second one has no input and no output
-- (but can have side effects), with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '<*'.
(/*)  :: SIArrow cat => cat () a -> cat () () -> cat () a
f /* g = unit /$/ f /*/ g

-- | The product of two arrows, where the first one has no input and no output
-- (but can have side effects), with duplicate units removed. Side effect are
-- sequenced from left to right.
--
-- The uncurried analogue of '*>'.
(*/)  :: SIArrow cat => cat () () -> cat () a -> cat () a
f */ g = unit . swapped /$/ f /*/ g

-- | An arrow that fails with an error message.
sifail :: SIArrow cat => String -> cat a b
sifail = arr . alwaysFailing

-- | Provides an error message in the case of failure.
(/?/) :: (SIArrow cat, Monoidal cat) => cat a b -> String -> cat a b
f /?/ msg = f /+/ sifail msg

-- | @sisome v@ repeats @v@ as long as possible, but no less then once.
sisome :: (SIArrow cat, Monoidal cat) => cat () b -> cat () [b]
sisome v = _Cons /$/ v /*/ simany v

-- | @simany v@ repeats @v@ as long as possible.
simany :: (SIArrow cat, Monoidal cat) => cat () b -> cat () [b]
simany v = sisome v /+/ rarr _Empty

-- | Equivalent of 'sequence'.
sisequence :: SIArrow cat => [cat () a] -> cat () [a]
sisequence [] = rarr _Empty
sisequence (x:xs) = _Cons /$/ x /*/ sisequence xs

-- | Equivalent of 'sequence_', restricted to units.
sisequence_ :: SIArrow cat => [cat () ()] -> cat () ()
sisequence_ [] = rarr _Empty
sisequence_ (x:xs) = unit /$/ x /*/ sisequence_ xs

-- | Equivalent of 'replicateM'.
sireplicate :: SIArrow cat => Int -> cat () a -> cat () [a]
sireplicate n f = sisequence (replicate n f)

-- | Equivalent of 'replicateM_', restricted to units.
sireplicate_ :: SIArrow cat => Int -> cat () () -> cat () ()
sireplicate_ n f = sisequence_ (replicate n f)
