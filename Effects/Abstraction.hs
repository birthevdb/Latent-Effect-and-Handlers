{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Abstraction where

import General

data Abstracting v :: * -> (* -> *) -> * where
  Var :: Int ->     Abstracting v v NoSub
  App :: v -> v ->  Abstracting v v NoSub
  Abs ::            Abstracting v v (OneSub v)

data Closure v where
  Clos :: Ptr -> Env v -> Closure v

type Env v = [v]
type Ptr = Int

type Store_CS  σ l v  = [R_CS σ l v]
type R_CS      σ l v  = l () -> Tree (Abstracting v :++: σ) l (l v)
type Store_DS  σ l v  = [R_DS σ l v]
type R_DS      σ l v  = Tree (Abstracting v :++: σ) l (l v)


handleAbsCS  :: (Closure v :<<<: v, Functor l)
             => [v]
             -> Store_CS σ l v
             -> Tree (Abstracting v :++: σ) l a
             -> Tree σ (StateL (Store_CS σ l v) l) (Store_CS σ l v, a)
handleAbsCS _   r (Leaf x) = Leaf (r, x)
handleAbsCS nv  r (Node (Inl' Abs) l st k) = do
  let v  = injV (Clos (length r) nv)
  let r' = r ++ [st One]
  handleAbsCS  nv r' (k (v <$ l))
handleAbsCS nv  r (Node (Inl' (App v1 v2)) l _ k)  = case projV v1 of
    Just (Clos fp nv')  -> do
      (r', v) <- handleAbsCS (v2:nv') r ((r !! fp) l)
      handleAbsCS nv r' (k v)
    Nothing             -> error "application error"
handleAbsCS nv r (Node (Inl' (Var n)) l _ k) = handleAbsCS nv r (k ((nv !! n) <$ l))
handleAbsCS nv r (Node (Inr' op) l st k) = Node op (StateL (r, l))
  (\c (StateL (r', l )) -> StateL <$> handleAbsCS nv r' (st c l))
  (\  (StateL (r', lv)) -> handleAbsCS nv r' (k lv))

handleAbsDS :: (Closure v :<<<: v , Functor l)
            => [v]
            -> Store_DS σ l v
            -> Tree (Abstracting v :++: σ) l a
            -> Tree σ (StateL (Store_DS σ l v) l) (Store_DS σ l v, a)
handleAbsDS _   r (Leaf x) = Leaf (r, x)
handleAbsDS nv  r (Node (Inl' Abs) l st k) = do
  let v  = injV (Clos (length r) nv)
  let r' = r ++ [st One l]
  handleAbsDS  nv r' (k (v <$ l))
handleAbsDS nv  r (Node (Inl' (App v1 v2)) _ _ k) =
  case projV v1 of
    Just (Clos fp nv') -> do
      (r', v) <- handleAbsDS (v2:nv') r (r !! fp)
      handleAbsDS nv r' (k v)
    Nothing -> error "application error"
handleAbsDS nv  r (Node (Inl' (Var n)) l _ k) =
  handleAbsDS nv r (k (nv !! n <$ l))
handleAbsDS nv  r (Node (Inr' op) l st k) =
  Node op (StateL (r, l))
       (\c (StateL (r', l)) ->
          StateL <$> handleAbsDS nv r' (st c l))
       (\(StateL (r', lv))  -> handleAbsDS nv r' (k lv))


var        :: (Abstracting v :<<: σ) => Int -> Tree σ Id v
var n      = noSubNode (Var n)

app        :: (Abstracting v :<<: σ) => v -> v -> Tree σ Id v
app v1 v2  = noSubNode (App v1 v2)

abs        :: (Abstracting v :<<: σ) => Tree σ Id v -> Tree σ Id v
abs t      = oneSubNode Abs t
