{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  Control.Lens.Internal.SemiIso
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
data Retail s t a b = Retail (a -> Either String s) (t -> Either String b)

instance Profunctor (Retail s t) where
    lmap f (Retail l r) = Retail (l . f) r
    rmap f (Retail l r) = Retail l (fmap f . r)

instance Choice (Retail s t) where
    left' (Retail as st) = Retail 
        (either as (\_ -> Left "semi-iso failed")) (fmap Left . st)
    right' (Retail as st) = Retail 
        (either (\_ -> Left "semi-iso failed") as) (fmap Right . st)

-- Proof of 'Exposed' laws:
--
-- > merge . rmap return = id
--
-- merge . rmap return $ Retail l r =
-- merge $ Retail l (return . r) =
-- Retail l (join . return . r) =
-- Retail l r
--
-- > lmap return . expose = id
--
-- lmap return . expose $ Retail l r =
-- lmap return $ Retail (>>= l) r =
-- Retail ((>>= l) . return) r =
-- Retail (join . fmap l . return) r =
-- Retail (join . return . l) r =
-- Retail l r
--
-- > rmap (>>= f) = merge . rmap (fmap f)
--
-- rmap (>>= f) $ Retail l r =
-- Retail l ((>>= f) . r) =
-- Retail l (join . fmap f . r) =
-- merge $ Retail l (fmap f . r) =
-- merge . rmap (fmap f) $ Retail l r
--
-- > lmap (fmap f) . expose = expose . lmap f
--
-- lmap (fmap f) . expose $ Retail l r =
-- lmap (fmap f) $ Retail (>>= l) r =
-- Retail ((>>= l) . fmap f) r =
-- Retail (>>= (l . f)) r =
-- expose $ Retail (l . f) r =
-- expose . lmap f $ Retail l r
instance Exposed (Either String) (Retail s t) where
    expose (Retail l r) = Retail (>>= l) r
    merge (Retail l r) = Retail l (join . r)
