{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Features.CallByNeed where

import General
import Effects.Abstraction
import Effects.Memoization
import Effects.Reader
import Effects.Delay

data LamExpr e = VarExpr Int | AbsExpr e | AppExpr e e


lazyAlg  :: (  Reading [v] :<<: σ, Thunking v :<<: σ, Suspending v :<<: σ,
               Thunked [v] :<<<: v, Closure v :<<<: v)
         => LamExpr (Tree σ Id v) -> Tree σ Id v
lazyAlg (VarExpr n)      = var_lazy n
lazyAlg (AbsExpr e)      = abs_lazy e
lazyAlg (AppExpr e1 e2)  = app_lazy e1 e2

var_lazy  :: forall v σ. (Reading [v] :<<: σ, Thunking v :<<: σ, Thunked [v] :<<<: v)
     => Int -> Tree σ Id v
var_lazy  x = do
  nv <- ask
  let v = (nv :: [v]) !! x
  case projV v of
    Just (Thunked p nv')  -> local (const (nv' :: [v])) (force p)
    Nothing               -> return v

abs_lazy  :: forall v σ. (Reading [v] :<<: σ, Suspending v :<<: σ, Closure v :<<<: v)
     => Tree σ Id v -> Tree σ Id v
abs_lazy body = do
  nv <- ask
  p <- suspend body
  return (injV (Clos p (nv :: [v])))

app_lazy  :: forall v σ. (Suspending v :<<: σ, Thunking v :<<: σ, Reading [v] :<<: σ,
                      Closure v :<<<: v, Thunked [v] :<<<: v)
     => Tree σ Id v -> Tree σ Id v -> Tree σ Id v
app_lazy e1 e2 = do
  vf <- e1; nv <- ask; p <- thunk e2
  let th :: v = injV $ Thunked p (nv :: [v])
  case projV vf of
    Just (Clos p' nv') -> do
      local (const (th : (nv' :: [v]))) (enact p')
