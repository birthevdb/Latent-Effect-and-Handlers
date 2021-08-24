{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Features.Arithmetics where

import General
import Effects.Arithmetics

data Arith n = Num Int | Add n n

arithAlg :: (Adding v :<<: σ) => Arith v -> Tree σ Id v
arithAlg (Num n)    = nat (toInteger n)
arithAlg (Add x y)  = plus x y
