{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Features.Let where

import General
import Effects.Abstraction

import Prelude hiding (abs)

data LetExpr e = Let e e | Seq e e | LetVar Int

letAlg :: (Abstracting v :<<: σ) => LetExpr (Tree σ Id v) -> Tree σ Id v
letAlg (Let e1 e2)  = do
  v1 <- abs e1
  v2 <- e2
  app v1 v2
letAlg (Seq e1 e2)  = do e1 ; e2
letAlg (LetVar n)   = var n
