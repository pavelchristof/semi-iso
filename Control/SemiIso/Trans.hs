{- |
Module      :  Control.SemiIso.Trans
Description :  SemiIsoMonad transformers.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Monad transformers for the SemiIso hierarchy.
-}
module Control.SemiIso.Trans where

import Data.SemiIsoFunctor

-- | Monad transformer. Should satisfy laws:
--
-- prop> silift . sipure = sipure
--
-- prop> silift (m //= f) = silift m //= (silift . f)
class SIMonadTrans t where
    -- | Lifts a computation from the base monad.
    silift :: SemiIsoMonad m => m a -> t m a
