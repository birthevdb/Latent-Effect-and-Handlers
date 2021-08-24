{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Features.Print where

import General
import Effects.Print

import Prelude hiding (print)

data PrintExpr e = Pr String

printAlg :: (Printing v :<<: σ) => PrintExpr v -> Tree σ Id v
printAlg (Pr s) = print s
