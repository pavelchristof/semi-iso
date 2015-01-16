{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{- |
Module      :  Control.Category.Reader
Description :  Reader category transformer.
Copyright   :  (c) Paweł Nowak
License     :  MIT

Maintainer  :  Paweł Nowak <pawel834@gmail.com>
Stability   :  experimental

Provides a Reader category transformer.
-}
module Control.Category.Reader (
    ReaderCT(..)
    ) where

import Control.Category
import Control.Category.Structures
import Control.Lens.Iso
import Control.Lens.SemiIso
import Control.SIArrow
import Prelude hiding (id, (.))

newtype ReaderCT env cat a b = ReaderCT { runReaderCT :: env -> cat a b }

instance CatTrans (ReaderCT env) where
    clift = ReaderCT . const

instance Category cat => Category (ReaderCT env cat) where
    id = clift id
    ReaderCT f . ReaderCT g = ReaderCT $ \x -> f x . g x

instance Products cat => Products (ReaderCT env cat) where
    ReaderCT f *** ReaderCT g = ReaderCT $ \x -> f x *** g x

instance Coproducts cat => Coproducts (ReaderCT env cat) where
    ReaderCT f +++ ReaderCT g = ReaderCT $ \x -> f x +++ g x

instance Monoidal cat => Monoidal (ReaderCT env cat) where
    cempty = clift cempty
    ReaderCT f /+/ ReaderCT g = ReaderCT $ \x -> f x /+/ g x

instance Dagger cat => Dagger (ReaderCT env cat) where
    dagger = ReaderCT . (dagger .) . runReaderCT

instance SubHask cat => SubHask (ReaderCT env cat) where
    type HaskRep (ReaderCT env cat) a b = env -> HaskRep cat a b
    toHask   = (toHask .) . runReaderCT
    fromHask = ReaderCT . (fromHask .)

instance GArrow cat => GArrow (ReaderCT env cat) where
    type Base (ReaderCT env cat) = Base cat
    arr = clift . arr

instance SIBind cat => SIBind (ReaderCT env cat) where
    sibind ai = ReaderCT $ \env -> sibind
        (iso id (flip runReaderCT env) . cloneSemiIso ai . iso (flip runReaderCT env) id)
