{- |
Module      :  Data.Lens.Internal.SemiIso
Description :  Internals of a SemiIso.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental
-}
module Control.Lens.Internal.SemiIso where

import Control.Monad
import Data.Profunctor

-- | Type used internally to access 'SemiIso'.
--
-- Continues the naming tradition of @lens@.
data Barter s t a b = Barter (a -> Either String s) (t -> Either String b)

instance Profunctor (Barter s t) where
    lmap f (Barter l r) = Barter (l . f) r
    rmap f (Barter l r) = Barter l (fmap f . r)

instance Choice (Barter s t) where
    left' (Barter as st) = Barter 
        (either as (\_ -> Left "partial iso failed")) (fmap Left . st)
    right' (Barter as st) = Barter 
        (either (\_ -> Left "partial iso failed") as) (fmap Right . st)

-- | Provides a profunctor the ability to fail with an error message.
--
-- This class could use some laws. It is certainly a bit ad-hoc.
class Profunctor p => Failure p where
    tie :: p a (Either String b) -> p a b
    attach :: p a b -> p (Either String a) b

instance Failure (Barter s t) where
    tie (Barter f g) = Barter f (join . g)
    attach (Barter f g) = Barter (>>= f) g
