{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Arithmetics where

import General

data Adding v :: * -> (* -> *) -> * where
  Nat   :: Integer  -> Adding v v NoSub
  Plus  :: v -> v   -> Adding v v NoSub

hPlus  :: (Functor l, Integer :<<<: v)
       => Tree (Adding v :++: σ) l a
       -> Tree σ l a
hPlus (Leaf x)                              = Leaf x
hPlus (Node (Inl' (Nat n))       l  _   k)  = hPlus (k (const (injV n) <$> l))
hPlus (Node (Inl' (Plus v1 v2))  l  _   k)  = case (projV v1, projV v2) of
  (Just n1, Just n2) -> hPlus (k (const (injV (n1 + n2)) <$> l))
hPlus (Node (Inr' c)             l  st  k)  =
  Node c l (\s -> hPlus . st s) (hPlus . k)

plus        :: (Adding v :<<: σ) => v -> v -> Tree σ Id v
plus n1 n2  = noSubNode (Plus n1 n2)

nat         :: (Adding v :<<: σ) => Integer -> Tree σ Id v
nat n       = noSubNode (Nat n)
