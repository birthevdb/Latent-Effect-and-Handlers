{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Delay where

import General

data Suspending v :: * -> (* -> *) -> * where
  Suspend  ::         Suspending v Ptr  (OneSub v)
  Enact    :: Ptr ->  Suspending v v    NoSub

type Ptr                = Int
type Suspension σ l v   = l () -> Tree (Suspending v :++: σ) l (l v)

data Suspended r        = Suspended Ptr r deriving (Functor)

hSuspend  :: Functor l
          => [Suspension σ l v]
          -> Tree (Suspending v :++: σ) l (l a)
          -> Tree σ (StateL [Suspension σ l v] l) (StateL [Suspension σ l v] l a)
hSuspend rs (Leaf x)                          = Leaf (StateL (rs, x))
hSuspend rs (Node (Inl' Suspend)    l st  k)  =
  hSuspend (rs ++ [st One]) (k (length rs <$ l))
hSuspend rs (Node (Inl' (Enact p))  l _   k)  = do
  StateL (rs', lv) <- hSuspend rs ((rs !! p) l);  hSuspend rs' (k lv)
hSuspend rs (Node (Inr' op)         l st  k)  =
  Node op (StateL (rs, l))  (\ c2  (StateL (rs', l'))   -> hSuspend rs' (st c2 l'))
                            (\     (StateL (rs', lv'))  -> hSuspend rs' (k lv'))

suspend    :: forall v σ. (Suspending v :<<: σ) => Tree σ Id v -> Tree σ Id Ptr
suspend t  = oneSubNode (Suspend) t

enact      :: (Suspending v :<<: σ) => Ptr -> Tree σ Id v
enact p    = noSubNode (Enact p)
