{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  Data.Profunctor.Exposed
Description :  Exposes Kleisli category structure beneath a profunctor.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental
-}
module Data.Profunctor.Exposed where

import Data.Profunctor

-- | Exposes structure of a Kleisli category beneath a profunctor.
-- 
-- Should obey laws:
-- 
-- prop> merge . rmap return = id
-- prop> lmap return . expose = id
-- prop> rmap (>>= f) = merge . rmap (fmap f)
-- prop> lmap (fmap f) . expose = expose . lmap f
class (Monad m, Profunctor p) => Exposed m p | p -> m where
    expose :: p a b -> p (m a) b
    merge  :: p a (m b) -> p a b 
