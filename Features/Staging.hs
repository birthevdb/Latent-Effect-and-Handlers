{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverlappingInstances #-}

module Features.Staging where

import General
import Effects.Delay hiding (Ptr)
import Effects.Reader
import Effects.Memoization
import Features.CallByValue

import Control.Monad
import Prelude hiding (lookup, abs)

data StageExpr s = Splice s | Quote s | Unquote s | Push Int s

stageAlg  :: forall v σ r1 r2 .
            (Suspending v :<<: σ, Reading r1 :<<: σ, Reading r2 :<<: σ,
             Reading (Env_s v) :<<: σ, Suspended r1 :<<<: v,
             Suspended r2 :<<<: v, Suspended (Env_s v) :<<<: v)
         => StageExpr (Tree σ Id v) -> Tree σ Id v
stageAlg (Splice s)  = splice s
stageAlg (Quote s)   = quote @r1 s
stageAlg (Unquote s) = unquote @r2 s
stageAlg (Push n s)  = push n s

-- Binding and looking up a variable in an environment

class Bindable r v where
  bindVal    :: v -> r -> r
  lookupVal  :: r -> Int -> v

instance Bindable [v] v where
  bindVal    = (:)
  lookupVal  = (!!)

data Closure' v where
  Clos' :: Ptr -> v -> Closure' v

-- quote and unquote
quote  :: forall r v l σ.
       (Reading r :<<: σ, Suspending v :<<: σ, Suspended r :<<<: v)
       => Tree σ Id v -> Tree σ Id v
quote m = do
  p   <- suspend m
  nv  <- ask
  return (injV $ Suspended p (nv :: r))

unquote  :: forall r v l σ.
         (Reading r :<<: σ, Suspending v :<<: σ, Suspended r :<<<: v)
         => Tree σ Id v -> Tree σ Id v
unquote m = do
  v <- m
  case projV v of
    Just (Suspended p nv)  -> local (const (nv :: r)) (enact p)
    Nothing                -> error "bad unquote"

newtype Env_s v = Env_s { unEnv_s :: [Maybe (Either v Int)] } deriving (Show)

data Val  = CloV (Closure'  (Env_s Val))
          | CodV (Suspended (Env_s Val))
          | IntV Int

instance Closure' (Env_s Val) :<<<: Val where
  injV c = CloV c
  projV (CloV c) = Just c
  projV _ = Nothing

instance Suspended (Env_s Val) :<<<: Val where
  injV c = CodV c
  projV (CodV c) = Just c
  projV _ = Nothing

instance Bindable (Env_s Val) Val where
  bindVal    v           (Env_s nv) = Env_s $ Just
           (Right (length nv)) : nv ++ [Just (Left v)]

  lookupVal  (Env_s nv)  x = go nv x
    where  go (Nothing         : nv)  0  = error "quote error"
           go (Just (Right y)  : nv)  0  = lookupVal (Env_s nv) y
           go (Just (Left v)   : nv)  0  = cover v (Env_s nv)
           go (_               : nv)  x  | x >= 0 = lookupVal (Env_s nv) (x - 1)
           go nv                      x  = error "bad index"

cover :: Val -> Env_s Val -> Val
cover (CloV (Clos' p nv'))      nv  = CloV (Clos'      p  (combine nv' nv))
cover (CodV (Suspended p nv'))  nv  = CodV (Suspended  p  (combine nv' nv))
cover (IntV i)                  nv  = IntV i

combine :: Env_s v -> Env_s v -> Env_s v
combine (Env_s nv1) (Env_s nv2) = Env_s (go nv1 nv2)
  where
    go []                nv                       = nv
    go (Nothing  : nv1)  []                       = Nothing : nv1
    go (Nothing  : nv1)  (Nothing         : nv2)  = Nothing : go nv1 nv2
    go (Nothing  : nv1)  (Just (Left v)   : nv2)  = Just (Left v) : go nv1 nv2
    go (Nothing  : nv1)  (Just (Right n)  : nv2)  = Just (Right (n + length nv1))
                                          : go nv1 nv2
    go (Just v   : nv1)  nv2                      = Just v : go nv1 nv2

push  :: forall v σ. (Reading (Env_s v) :<<: σ)
       => Int -> Tree σ Id v -> Tree σ Id v
push n m = local  (\ (Env_s nv :: Env_s v) ->
                         Env_s $ replicate n Nothing ++ nv)
                   m

splice  :: forall r v l σ. (  Reading (Env_s v) :<<: σ, Suspending v :<<: σ,
                              Suspended (Env_s v) :<<<: v)
        => Tree σ Id v -> Tree σ Id v
splice m = do
  v <- m
  case projV v of
    Just (Suspended p nv)  -> local (combine (nv :: Env_s v)) (enact p)
    Nothing                -> error "bad unquote"

type Ops  =  Thunking Val  :++:  Suspending Val :++:  Reading (Env_s Val) :++:  Voiding

instance Modular Id m where
  fwd = id . unId

operate :: Tree Ops Id a -> a
operate t =
  case hRead (Env_s [])
     $ hSuspend []
     $ hThunk [] (Id <$> t) of
    Leaf (StateL (_, StateL (_, x))) -> unId x

abs_cbv  :: forall r v σ.
          (Suspending v :<<: σ, Reading r :<<: σ, Closure' r :<<<: v)
          => Tree σ Id v -> Tree σ Id v
abs_cbv body = do
  p <- suspend body; nv <- ask
  return (injV (Clos' p (nv :: r)))

app_cbv  :: forall r v σ.
         (Suspending v :<<: σ, Reading r :<<: σ, Closure' r :<<<: v, Bindable r v)
         => Tree σ Id v -> Tree σ Id v -> Tree σ Id v
app_cbv m1 m2 = do
  vf <- m1; v  <- m2; case projV vf of
    Just (Clos' p nv) -> do
      local (const (bindVal v (nv :: r))) (enact p)
    _ -> error "bad application"

var_cbv  :: forall r v σ.
          (Reading r :<<: σ, Bindable r v)
          => Int -> Tree σ Id v
var_cbv x = do nv <- ask; return (lookupVal (nv :: r) x)

letbind :: Tree Ops Id Val -> Tree Ops Id Val -> Tree Ops Id Val
letbind me mb =
  app_cbv @(Env_s Val) (abs_cbv @(Env_s Val) mb) me

var' :: Int -> Tree Ops Id Val
var' x = var_cbv @(Env_s Val) x

app' :: Tree Ops Id Val -> Tree Ops Id Val -> Tree Ops Id Val
app' = app_cbv @(Env_s Val)

abs' :: Tree Ops Id Val -> Tree Ops Id Val
abs' = abs_cbv @(Env_s Val)

quote' :: Tree Ops Id Val -> Tree Ops Id Val
quote' = quote @(Env_s Val)

unquote' :: Tree Ops Id Val -> Tree Ops Id Val
unquote' = unquote @(Env_s Val) @Val

splice' :: Tree Ops Id Val -> Tree Ops Id Val
splice' = splice @(Env_s Val) @Val

add :: Tree Ops Id Val -> Tree Ops Id Val -> Tree Ops Id Val
add m1 m2 = do
  v1 <- m1
  v2 <- m2
  case (v1, v2) of
    (IntV i1, IntV i2) -> return (IntV (i1 + i2))

-- run (let T = λ e → < λ x → x + ~ e >
--      in < λ x → ~(T <x>) >)
--     1 2
taha :: Tree Ops Id Val
taha =
  letbind {-T-}
    (abs' {-e-}
      (letbind {-d0-}
        (push {-x-} 1 (var' {-x-} 1))
        (quote'
          (abs' {-x-} (add (var' {-x-} 0) (splice' (var' {-d0-} 1)))))))
    (letbind {-d1-}
      (push {-x-} 1 (app'  (var' {-T-} 1)
                           (quote' (var' {-x-} 0))))
      (quote' (abs' {-x-} (splice' (var' {-d1-} 1)))))

-- run (let puzzle = <λ a -> ~( (λ x -> <x>) (λ x -> <a>)) 0>
--      in (run puzzle) 5)
puzzle :: Tree Ops Id Val
puzzle =
  unquote' $
  letbind {-puzzle-} (letbind {-d0-} (push 1 (app'
                                                (abs' {-x-} (quote' (var' {-x-} 0)))
                                                (abs' {-x-} (quote' (var' {-a-} 1)))))
                       (quote' (abs' {-a-} (app'
                                             (splice' (var' {-d0-} 1))
                                             (return $ IntV 0))))) $
    app'
      (unquote' (var' {-puzzle-} 0))
      (return $ IntV 5)

run_taha :: Tree Ops Id Val
run_taha = app' (app' (unquote' taha) (return (IntV 1))) (return (IntV 2))
