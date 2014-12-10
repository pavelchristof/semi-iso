{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{- |
Module      :  Control.SIArrow
Description :  Semi-iso arrows.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

It can be instantiated by both covariant (like Parser) and contravariant 
(like Printer) functors. Therefore it can be used as a common interface to unify
parsing and pretty printing.
-}
module Control.SIArrow where

import           Control.Arrow (Kleisli(..))
import qualified Control.Arrow as BadArrow
import           Control.Category
import           Control.Lens.Cons
import           Control.Lens.Empty
import           Control.Lens.SemiIso
import           Control.Monad
import           Data.Tuple.Morph
import           Prelude hiding (id, (.))

infixr 3 ***
infixr 2 +++
infixl 3 /+/
infixr 1 ^>>, >>^
infixr 1 ^<<, <<^
infixl 4 /$/, /$~, ~$/, ~$~
infixl 5 /*/, */, /*

-- Categories.

class Category cat => Products cat where
    first :: cat a b -> cat (a, c) (b, c)
    first a = a *** id

    second :: cat a b -> cat (c, a) (c, b)
    second a = id *** a

    (***) :: cat a b -> cat c d -> cat (a, c) (b, d)
    a *** b = first a >>> second b

class Category cat => Coproducts cat where
    left :: cat a b -> cat (Either a c) (Either b c)
    left a = a +++ id

    right :: cat a b -> cat (Either c a) (Either c b)
    right a = id +++ a

    (+++) :: cat a b -> cat c d -> cat (Either a c) (Either b d)
    a +++ b = left a >>> right b

class Category cat => CategoryPlus cat where
    cempty :: cat a b
    (/+/) :: cat a b -> cat a b -> cat a b

class (Products cat, Coproducts cat, CategoryPlus cat) => SIArrow cat where
    siarr :: ASemiIso' a b -> cat a b

    sipure :: ASemiIso' b a -> cat a b
    sipure = siarr . rev

    sisome :: cat () b -> cat () [b]
    sisome v = _Cons /$/ v /*/ simany v

    simany :: cat () b -> cat () [b]
    simany v = sisome v /+/ sipure _Empty

class CategoryTrans t where
    clift :: Category cat => cat a b -> t cat a b

-- Kleisli instances.

instance Monad m => Products (Kleisli m) where
    (***) = (BadArrow.***)

instance Monad m => Coproducts (Kleisli m) where
    (+++) = (BadArrow.+++)

instance MonadPlus m => CategoryPlus (Kleisli m) where
    cempty = BadArrow.zeroArrow
    (/+/)  = (BadArrow.<+>)

instance MonadPlus m => SIArrow (Kleisli m) where
    siarr ai = Kleisli $ either fail return . apply ai

(^>>) :: SIArrow cat => ASemiIso' a b -> cat b c -> cat a c
f ^>> a = a . siarr f

(>>^) :: SIArrow cat => cat a b -> ASemiIso' b c -> cat a c
a >>^ f = siarr f . a

(^<<) :: SIArrow cat => ASemiIso' b c -> cat a b -> cat a c
f ^<< a = siarr f . a

(<<^) :: SIArrow cat => cat b c -> ASemiIso' a b -> cat a c
a <<^ f = a . siarr f

(/$/) :: SIArrow cat => ASemiIso' b' b -> cat a b -> cat a b'
ai /$/ f = sipure ai . f

-- | > ai /$~ f = ai . morphed /$/ f
--
-- This operator handles all the hairy stuff with uncurried application:
-- it reassociates the argument tuple and removes unnecessary (or adds necessary)
-- units to match the function type. You don't have to use @/*@ and @*/@ with this
-- operator. 
(/$~) :: (SIArrow cat, HFoldable b', HFoldable b,
           HUnfoldable b', HUnfoldable b, Rep b' ~ Rep b)
       => ASemiIso' a b' -> cat c b -> cat c a
ai /$~ h = cloneSemiIso ai . morphed /$/ h

-- | > ai ~$/ f = morphed . ai /$/ f
(~$/) :: (SIArrow cat, HFoldable a', HFoldable a,
          HUnfoldable a', HUnfoldable a, Rep a' ~ Rep a)
      => ASemiIso' a' b -> cat c b -> cat c a
ai ~$/ h = morphed . cloneSemiIso ai /$/ h

-- | > ai ~$~ f = morphed . ai . morphed /$/ f
(~$~) :: (SIArrow cat,
          HFoldable a, HUnfoldable a,
          HFoldable b, HUnfoldable b,
          HFoldable b', HUnfoldable b',
          Rep b' ~ Rep b, Rep b' ~ Rep a)
      => ASemiIso b' b' b' b' -> cat c b -> cat c a
ai ~$~ h = morphed . cloneSemiIso ai . morphed /$/ h

(/*/) :: SIArrow cat => cat () b -> cat () c -> cat () (b, c)
a /*/ b = unit ^>> (a *** b)

(/*)  :: SIArrow cat => cat () a -> cat () () -> cat () a
f /* g = unit /$/ f /*/ g

(*/)  :: SIArrow cat => cat () () -> cat () a -> cat () a
f */ g = unit . swapped /$/ f /*/ g

sifail :: SIArrow cat => String -> cat a b
sifail = siarr . alwaysFailing

-- | Provides an error message in the case of failure.
(/?/) :: SIArrow cat => cat a b -> String -> cat a b
f /?/ msg = f /+/ sifail msg

-- | Equivalent of 'sequence'.
sisequence :: SIArrow cat => [cat () a] -> cat () [a]
sisequence [] = sipure _Empty
sisequence (x:xs) = _Cons /$/ x /*/ sisequence xs

-- | Equivalent of 'sequence_', restricted to units.
sisequence_ :: SIArrow cat => [cat () ()] -> cat () ()
sisequence_ [] = sipure _Empty
sisequence_ (x:xs) = unit /$/ x /*/ sisequence_ xs

-- | Equivalent of 'replicateM'.
sireplicate :: SIArrow cat => Int -> cat () a -> cat () [a]
sireplicate n f = sisequence (replicate n f)

-- | Equivalent of 'replicateM_', restricted to units.
sireplicate_ :: SIArrow cat => Int -> cat () () -> cat () ()
sireplicate_ n f = sisequence_ (replicate n f)
