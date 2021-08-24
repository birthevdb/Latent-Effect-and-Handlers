{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Memoization where

import General

data Thunking v :: * -> (* -> *) -> * where
  Thunk  ::         Thunking v Ptr (OneSub v)
  Force  :: Ptr ->  Thunking v v   NoSub

type Ptr = Int

type Thunk σ l v = Either (l () -> Tree (Thunking v :++: σ) l (l v)) v

data TreeWith f σ (l :: * -> *) a =
  TreeWith { unTreeWith :: Tree σ (f l) (f l a) }
data Thunked r  = Thunked Ptr r

class Modular (m1 :: * -> *) (m2 :: (* -> *) -> * -> *) where
  fwd :: m1 (m2 m1 a) -> m2 m1 a

replace :: Int -> a -> [a] -> [a]
replace 0 x (_ : xs)          = x : xs
replace i x (y : xs) | i > 0  = y : replace (i - 1) x xs
replace _ _ _                 = error "bad index"

hThunk  :: (Functor l, Modular l (TreeWith (StateL ([Thunk σ l v])) σ))
        => [Thunk σ l v]
        -> Tree (Thunking v :++: σ) l (l a)
        -> Tree σ (StateL [Thunk σ l v] l) (StateL [Thunk σ l v] l a)
hThunk rs (Leaf x)                          = Leaf (StateL (rs, x))
hThunk rs (Node (Inl' Thunk)      l st  k)  =
  hThunk (rs ++ [Left (st One)]) (k (length rs <$ l))
hThunk rs (Node (Inl' (Force p))  l _   k)  = case (rs !! p) of
  Left t -> do
    StateL (rs', lv) <- hThunk rs (t l)
    unTreeWith $ fwd $
      (\ v -> TreeWith $ hThunk (replace p (Right v) rs') (k lv)) <$> lv
  Right v -> hThunk rs (k (v <$ l))
hThunk rs (Node (Inr' op)         l st  k)  =
  Node op (StateL (rs, l)) (\ c2 (StateL (rs', l'))  -> hThunk rs' (st c2 l'))
                           (\    (StateL (rs', lv')) -> hThunk rs' (k lv'))

hEager  :: (Functor l, Modular l (TreeWith (StateL [v]) σ))
        => [v]
        -> Tree (Thunking v :++: σ) l (l a)
        -> Tree σ (StateL [v] l) (StateL [v] l a)
hEager vs (Leaf x)                        = Leaf (StateL (vs, x))
hEager vs (Node (Inl' Thunk)      l st k) = do
  StateL (vs', lv) <- hEager vs (st One l)
  unTreeWith $ fwd $
    (\ v -> TreeWith $ hEager (vs' ++ [v]) (k (length vs' <$ l))) <$> lv
hEager vs (Node (Inl' (Force p))  l _  k) = do
  hEager vs (k ((vs !! p) <$ l))
hEager vs (Node (Inr' op)         l st k) =
  Node op (StateL (vs, l)) (\ c2 (StateL (vs', l'))  -> hEager vs' (st c2 l'))
                           (\    (StateL (vs', lv')) -> hEager vs' (k lv'))


thunk    :: forall v σ. (Thunking v :<<: σ) => Tree σ Id v -> Tree σ Id Ptr
thunk t  = oneSubNode Thunk t

force    :: (Thunking v :<<: σ) => Ptr -> Tree σ Id v
force p  = noSubNode (Force p)
