{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.State where

import General

data Mutating v :: * -> (* -> *) -> * where
  Get  ::       Mutating v v   NoSub
  Put  :: v ->  Mutating v ()  NoSub

hState  ::  Functor l
        => s
        -> Tree (Mutating s :++: σ) l a
        -> Tree σ (StateL s l) (StateL s Id a)
hState s (Leaf x)                      = Leaf $ StateL (s, Id x)
hState s (Node (Inl' Get)     l  _  k) = hState s (k (fmap (\ _ -> s) l))
hState _ (Node (Inl' (Put s)) l  _  k) = hState s (k l)
hState s (Node (Inr' c)       l  st k) =
  Node c (StateL (s, l)) (\c (StateL (s', l'))  -> transS <$> hState s' (st c l'))
                         (\  (StateL (s', lv')) -> hState s' (k lv'))

transS :: StateL s Id (l a) -> StateL s l a
transS (StateL (s, x)) = StateL (s, unId x)

get    :: (Mutating s :<<: σ) => Tree σ Id s
get    = noSubNode Get

put    :: (Mutating s :<<: σ) => s -> Tree σ Id ()
put s  = noSubNode (Put s)
