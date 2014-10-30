{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Profunctor.Exposed

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

-- Proof of 'Exposed' laws:
--
-- > merge . rmap return = id
--
-- merge . rmap return $ Barter l r =
-- merge $ Barter l (return . r) =
-- Barter l (join . return . r) =
-- Barter l r
--
-- > lmap return . expose = id
--
-- lmap return . expose $ Barter l r =
-- lmap return $ Barter (>>= l) r =
-- Barter ((>>= l) . return) r =
-- Barter (join . fmap l . return) r =
-- Barter (join . return . l) r =
-- Barter l r
--
-- > rmap (>>= f) = merge . rmap (fmap f)
--
-- rmap (>>= f) $ Barter l r =
-- Barter l ((>>= f) . r) =
-- Barter l (join . fmap f . r) =
-- merge $ Barter l (fmap f . r) =
-- merge . rmap (fmap f) $ Barter l r
--
-- > lmap (fmap f) . expose = expose . lmap f
--
-- lmap (fmap f) . expose $ Barter l r =
-- lmap (fmap f) $ Barter (>>= l) r =
-- Barter ((>>= l) . fmap f) r =
-- Barter (>>= (l . f)) r =
-- expose $ Barter (l . f) r =
-- expose . lmap f $ Barter l r
instance Exposed (Either String) (Barter s t) where
    expose (Barter l r) = Barter (>>= l) r
    merge (Barter l r) = Barter l (join . r)
