{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  Data.SemiIsoFunctor.Wrapped
Description :  SemiIso instances for wrapped monads.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Every monad (with fail) is a SemiIsoMonad.
-}
module Data.SemiIsoFunctor.Wrapped where

import Control.Applicative
import Control.Lens.SemiIso
import Control.Monad
import Data.SemiIsoFunctor

-- | A wrapped covariant functor.
newtype WrappedCovariant m a = WrappedCovariant { runCovariant :: m a }
    deriving (Functor, Applicative, Alternative, Monad)

instance Monad m => SemiIsoFunctor (WrappedCovariant m) where
    simapCo ai m = m >>= either fail return . apply ai

instance Monad m => SemiIsoApply (WrappedCovariant m) where
    sipure ai = either fail return (unapply ai ())
    f /*/ g = liftM2 (,) f g

instance (Monad m, Alternative m) => SemiIsoAlternative (WrappedCovariant m) where
    siempty = empty
    f /|/ g = f <|> g

instance Monad m => SemiIsoMonad (WrappedCovariant m) where
    f //= g = f >>= (\x -> g x >>= \y -> return (x, y))
