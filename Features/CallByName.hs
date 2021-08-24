{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Features.CallByName where

import General
import Effects.Abstraction
import Effects.Delay
import Effects.Reader

data LamExpr e = VarExpr Int | AbsExpr e | AppExpr e e

cbnAlg  :: (  Reading [v] :<<: σ, Suspending v :<<: σ,
               Suspended [v] :<<<: v, Closure v :<<<: v)
         => LamExpr (Tree σ Id v) -> Tree σ Id v
cbnAlg (VarExpr n)      = var_cbn n
cbnAlg (AbsExpr e)      = abs_cbn e
cbnAlg (AppExpr e1 e2)  = app_cbn e1 e2

var_cbn  :: forall v σ. (Reading [v] :<<: σ, Suspending v :<<: σ, Suspended [v] :<<<: v)
     => Int -> Tree σ Id v
var_cbn  x = do
  nv <- ask
  let v = (nv :: [v]) !! x
  case projV v of
    Just (Suspended p nv')  -> local (const (nv' :: [v])) (enact p)
    Nothing                 -> return v

abs_cbn  :: forall v σ. (Reading [v] :<<: σ, Suspending v :<<: σ, Closure v :<<<: v)
         => Tree σ Id v -> Tree σ Id v
abs_cbn body = do
  nv  <- ask
  p   <- suspend body
  return (injV (Clos p (nv :: [v])))

app_cbn  :: forall v σ.  (Suspending v :<<: σ, Reading [v] :<<: σ,
                         Closure v :<<<: v, Suspended [v] :<<<: v)
     => Tree σ Id v -> Tree σ Id v -> Tree σ Id v
app_cbn e1 e2 = do
  vf <- e1; nv <- ask; p <- suspend e2
  let th :: v = injV $ Suspended p (nv :: [v])
  case projV vf of
    Just (Clos p' nv') -> do
      local (const (th : (nv' :: [v]))) (enact p')
