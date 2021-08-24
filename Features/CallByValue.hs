{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Features.CallByValue where

import General
import Effects.Abstraction

import Prelude hiding (abs)

data LamExpr e = VarExpr Int | AbsExpr e | AppExpr e e

lamAlg :: (Abstracting v :<<: σ) => LamExpr (Tree σ Id v) -> Tree σ Id v
lamAlg (VarExpr n)      = var n
lamAlg (AbsExpr e)      = abs e
lamAlg (AppExpr e1 e2)  = do
  v1 <- e1
  v2 <- e2
  app v1 v2
