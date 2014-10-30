{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{- |
Module      :  Data.Lens.SemiIso
Description :  Semi-isomorphisms.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Semi-isomorphisms were motivated by reversible parsing/pretty printing. For example
we can map a number 12 to a string "12" (and the other way around). But the isomorphism
is partial - we cannot map the string "forty-two" to a number.

Another example: when parsing a list of numbers like "12_53___42" we want to skip underscores
between numbers (and forget about them). During pretty printing we have to decide how many
underscores should we insert between numbers. Let's say we insert a single underscore. But now
@prettyPrint (parse "12_53___42") = "12_53_42"@ and not "12_53___42". We have to weaken
isomorphism laws to allow such semi-iso. Notice that

> parse (prettyPrint (parse "12_53___42"))       = parse "12_53___42"
> prettyPrint (parse (prettyPrint [12, 53, 42])) = prettyPrint [12, 53, 42]

Our semi-isomorphisms will obey weakened laws:

> apply i   >=> unapply i >=> apply i   = apply i
> unapply i >=> apply i   >=> unapply i = unapply i

When you see an "Either String a", the String is usually an error message.

Disclaimer: the name "semi-isomorphism" is fictitious and made up for this library. 
Any resemblance to known mathematical objects of the same name is purely coincidental.
-}
module Control.Lens.SemiIso (
    -- * Semi-isomorphism types.
    SemiIso,
    SemiIso',
    ASemiIso,
    ASemiIso',
    
    -- * Constructing semi-isos.
    semiIso,

    -- * Consuming semi-isos.
    withSemiIso,
    fromSemi,
    apply,
    unapply,
    
    -- * Common semi-isomorphisms and isomorphisms.
    unit,
    swapped,
    associated,
    constant,
    exact,

    -- * Folds.
    bifoldr
    ) where

import Control.Lens.Internal.SemiIso
import Control.Lens.Iso
import Control.Monad
import Data.Functor.Identity
import Data.Traversable
import Data.Foldable

-- | A semi-isomorphism is a partial isomorphism with weakened laws.
-- 
-- Should satisfy laws:
-- 
-- > apply i   >=> unapply i >=> apply i   = apply i
-- > unapply i >=> apply i   >=> unapply i = unapply i
--
-- Every 'Prism' is a 'SemiIso'.
-- Every 'Iso' is a 'Prism'.
type SemiIso s t a b = forall p f. (Failure p, Traversable f) => p a (f b) -> p s (f t)

-- | Non-polymorphic variant of 'SemiIso'.
type SemiIso' s a = SemiIso s s a a

-- | When you see this as an argument to a function, it expects a 'SemiIso'.
type ASemiIso s t a b = Barter a b a (Identity b) -> Barter a b s (Identity t)

-- | When you see this as an argument to a function, it expects a 'SemiIso''.
type ASemiIso' s a = ASemiIso s s a a

-- | Constructs a semi isomorphism from a pair of functions that can
-- fail with an error message.
semiIso :: (s -> Either String a) -> (b -> Either String t) -> SemiIso s t a b
semiIso sa bt = tie . dimap sa (sequenceA . fmap bt) . attach

-- | Extracts the two functions that characterize the 'SemiIso'.
withSemiIso :: ASemiIso s t a b 
            -> ((s -> Either String a) -> (b -> Either String t) -> r) 
            -> r
withSemiIso ai k = case ai (Barter Right (Right . Identity)) of
                        Barter sa bt -> k sa (rmap (runIdentity . sequenceA) bt)

-- | Applies the 'SemiIso'.
apply :: ASemiIso s t a b -> s -> Either String a
apply ai = withSemiIso ai $ \l _ -> l

-- | Applies the 'SemiIso' in the opposite direction.
unapply :: ASemiIso s t a b -> b -> Either String t
unapply ai = withSemiIso ai $ \_ r -> r

-- | Reverses a 'SemiIso'.
fromSemi :: ASemiIso s t a b -> SemiIso b a t s
fromSemi ai = withSemiIso ai $ \l r -> semiIso r l

-- | A trivial isomorphism between a and (a, ()).
unit :: Iso' a (a, ())
unit = iso (, ()) fst

-- | Products are associative.
associated :: Iso' (a, (b, c)) ((a, b), c)
associated = iso (\(a, (b, c)) -> ((a, b), c)) (\((a, b), c) -> (a, (b, c)))

-- | \-> Always returns the argument.
--
-- \<- Maps everything to a @()@.
--
-- Note that this isn't an @Iso'@ because
--
-- > unapply (constant x) >=> apply (constant x) /= id
--
-- But SemiIso laws do hold.
constant :: a -> SemiIso' () a
constant x = semiIso (\_ -> Right x) (\_ -> Right ())

-- | \-> Always returns the argument.
--
-- \<- Filters out all values not equal to the argument.
exact :: Eq a => a -> SemiIso' () a
exact x = semiIso f g
  where
    f _ = Right x
    g y | x == y    = Right ()
        | otherwise = Left "exact: not equal"

-- | Constructs a bidirectional fold.
--
-- \-> Right folds using the (->) part of the given semi-iso.
--
-- \<- Right unfolds using the (<-) part of the given semi-iso.
bifoldr :: ASemiIso (b, a) (Maybe (b, a)) a a -> SemiIso' (a, [b]) a
bifoldr ai = semiIso (f ai) (g ai)
  where
    f = uncurry . foldrM . curry . apply
    g = unfoldrM . unapply

    unfoldrM :: Monad m => (a -> m (Maybe (b, a))) -> a -> m (a, [b])
    unfoldrM f a = do
        r <- f a
        case r of
          Just (b, new_a) -> do
              (final_a, bs) <- unfoldrM f new_a
              return (final_a, b : bs)
          Nothing -> return (a, [])