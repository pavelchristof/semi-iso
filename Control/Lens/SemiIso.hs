{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  Control.Lens.SemiIso
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

    -- * Transforming semi-isos.
    withSemiIso,
    attempt,
    attemptAp,
    attemptUn,
    attempt_,
    attemptAp_,
    attemptUn_,

    -- * Consuming semi-isos.
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
    foldlM1,
    foldrM1,
    unfoldlM,
    unfoldlM1,
    unfoldrM,
    unfoldrM1,

    -- * Bidirectional folds.
    bifoldr,
    bifoldr1,
    bifoldl,
    bifoldl1,

    -- * Profunctor.
    Profunctor(..),
    Exposed(..)
    ) where

import Control.Lens.Internal.SemiIso
import Control.Lens.Iso
import Data.Foldable
import Data.Functor.Identity
import Data.Profunctor.Exposed
import Data.Traversable

-- | A semi-isomorphism is a partial isomorphism with weakened laws.
-- 
-- Should satisfy laws:
-- 
-- > apply i   >=> unapply i >=> apply i   = apply i
-- > unapply i >=> apply i   >=> unapply i = unapply i
--
-- Every 'Prism' is a 'SemiIso'.
-- Every 'Iso' is a 'Prism'.
type SemiIso s t a b = forall p f. (Exposed (Either String) p, Traversable f) => p a (f b) -> p s (f t)

-- | Non-polymorphic variant of 'SemiIso'.
type SemiIso' s a = SemiIso s s a a

-- | When you see this as an argument to a function, it expects a 'SemiIso'.
type ASemiIso s t a b = Retail a b a (Identity b) -> Retail a b s (Identity t)

-- | When you see this as an argument to a function, it expects a 'SemiIso''.
type ASemiIso' s a = ASemiIso s s a a

-- | Constructs a semi isomorphism from a pair of functions that can
-- fail with an error message.
semiIso :: (s -> Either String a) -> (b -> Either String t) -> SemiIso s t a b
semiIso sa bt = merge . dimap sa (sequenceA . fmap bt) . expose

-- | Extracts the two functions that characterize the 'SemiIso'.
withSemiIso :: ASemiIso s t a b 
            -> ((s -> Either String a) -> (b -> Either String t) -> r) 
            -> r
withSemiIso ai k = case ai (Retail Right (Right . Identity)) of
                        Retail sa bt -> k sa (rmap (runIdentity . sequenceA) bt)

attempt :: ASemiIso s t a b -> SemiIso s (Either String t) (Either String a) b
attempt = attemptAp . attemptUn

attemptAp :: ASemiIso s t a b -> SemiIso s t (Either String a) b
attemptAp = undefined 

attemptUn :: ASemiIso s t a b -> SemiIso s (Either String t) a b
attemptUn = undefined

discard :: Either a b -> Maybe b
discard = either (const Nothing) Just

attempt_ :: ASemiIso s t a b -> SemiIso s (Maybe t) (Maybe a) b
attempt_ ai = rmap (fmap discard) . attempt ai . lmap discard

attemptAp_ :: ASemiIso s t a b -> SemiIso s t (Maybe a) b
attemptAp_ ai = attemptAp ai . lmap discard

attemptUn_ :: ASemiIso s t a b -> SemiIso s (Maybe t) a b
attemptUn_ ai = rmap (fmap discard) . attemptUn ai

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

-- | Monadic counterpart of 'foldl1' (or non-empty list counterpart of 'foldlM').
foldlM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldlM1 f (x:xs) = foldlM f x xs
foldlM1 _ []     = fail "foldlM1: empty list"

-- | Monadic counterpart of 'foldr1' (or non-empty list counterpart of 'foldrM').
foldrM1 :: Monad m => (a -> a -> m a) -> [a] -> m a
foldrM1 _ [x]    = return x
foldrM1 f (x:xs) = foldrM1 f xs >>= f x
foldrM1 _ []     = fail "foldrM1: empty list"

-- | Monadic counterpart of 'unfoldr'.
unfoldrM :: Monad m => (a -> m (Maybe (b, a))) -> a -> m (a, [b])
unfoldrM f a = do
    r <- f a
    case r of
      Just (b, new_a) -> do
          (final_a, bs) <- unfoldrM f new_a
          return (final_a, b : bs)
      Nothing -> return (a, [])

-- | A variant of 'unfoldrM' that always produces a non-empty list.
unfoldrM1 :: Monad m => (a -> m (Maybe (a, a))) -> a -> m [a]
unfoldrM1 f a = do
    r <- f a
    case r of
      Just (b, new_a) -> do
          bs <- unfoldrM1 f new_a
          return (b : bs)
      Nothing -> return [a]

-- | Monadic counterpart of 'unfoldl'.
unfoldlM :: Monad m => (a -> m (Maybe (a, b))) -> a -> m (a, [b])
unfoldlM f a0 = go a0 []
  where
    go a bs = do
        r <- f a
        case r of
          Just (new_a, b) -> go new_a (b : bs)
          Nothing -> return (a, bs)

-- | A variant of 'unfoldlM' that always produces a non-empty list.
unfoldlM1 :: Monad m => (a -> m (Maybe (a, a))) -> a -> m [a]
unfoldlM1 f a0 = go a0 []
  where
    go a bs = do
        r <- f a
        case r of
          Just (new_a, b) -> go new_a (b : bs)
          Nothing -> return (a : bs)

-- | Constructs a bidirectional fold.
--
-- \-> Right unfolds using the (->) part of the given semi-iso.
--
-- \<- Right folds using the (<-) part of the given semi-iso.
bifoldr :: ASemiIso a a (Maybe (b, a)) (b, a) -> SemiIso' a (a, [b])
bifoldr ai = semiIso (uf ai) (f ai)
  where
    f = uncurry . foldrM . curry . unapply
    uf = unfoldrM . apply

-- | Constructs a bidirectional fold.
--
-- \-> Right unfolds using the (->) part of the given semi-iso. It should
-- produce an non-empty list.
--
-- \<- Right folds a non-empty list using the (<-) part of the given semi-iso.
bifoldr1 :: ASemiIso a a (Maybe (a, a)) (a, a) -> SemiIso' a [a]
bifoldr1 ai = semiIso (uf ai) (f ai)
  where
    f = foldrM1 . curry . unapply
    uf = unfoldrM1 . apply

-- | Constructs a bidirectional fold.
--
-- \-> Left unfolds using the (->) part of the given semi-iso.
--
-- \<- Left folds using the (<-) part of the given semi-iso.
bifoldl :: ASemiIso a a (Maybe (a, b)) (a, b) -> SemiIso' a (a, [b])
bifoldl ai = semiIso (uf ai) (f ai)
  where
    f = uncurry . foldlM . curry . unapply
    uf = unfoldlM . apply

-- | Constructs a bidirectional fold.
--
-- \-> Left unfolds using the (->) part of the given semi-iso. It should
-- produce an non-empty list.
--
-- \<- Left folds a non-empty list using the (<-) part of the given semi-iso.
bifoldl1 :: ASemiIso a a (Maybe (a, a)) (a, a) -> SemiIso' a [a]
bifoldl1 ai = semiIso (uf ai) (f ai)
  where
    f = foldlM1 . curry . unapply
    uf = unfoldlM1 . apply
