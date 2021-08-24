{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Reader where

import General

data Reading r ::  * -> (* -> *) -> * where
  Local  :: (r -> r) ->  Reading r a (OneSub a)
  Ask    ::              Reading r r NoSub

hRead  :: Functor l
       => r
       -> Tree (Reading r :++: σ) l (l a)
       -> Tree σ l (l a)
hRead r (Leaf x)                           = Leaf x
hRead r (Node (Inl' (Local f))  l  st  k)  = hRead (f r) (st One l) >>= hRead r . k
hRead r (Node (Inl' Ask)        l  _   k)  = hRead r (k (r <$ l))
hRead r (Node (Inr' op)         l  st  k)  =
  Node op l  (\ c2 -> hRead r . st c2) (hRead r . k)

local      :: forall r σ a. (Reading r :<<: σ) => (r -> r) -> Tree σ Id a -> Tree σ Id a
local f t  = oneSubNode (Local f) t

ask        :: (Reading r :<<: σ) => Tree σ Id r
ask        = noSubNode Ask
