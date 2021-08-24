{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}

module Effects.Errors where

import Prelude hiding (either)

import General

data Failing v :: * -> (* -> *) -> * where
  Err :: v -> Failing v Void NoSub

hErr  :: Functor l
      => Tree (Failing v :++: σ) l a
      -> Tree σ (EitherL v l) (EitherL v Id a)
hErr (Leaf x)                         = Leaf $ EitherL $ Right $ Id x
hErr (Node (Inl' (Err x))  _  _   _)  = Leaf $ EitherL $ Left x
hErr (Node (Inr' c)        l  st  k)  =
  Node c (EitherL $ Right l)
         (\z -> either (Leaf . EitherL . Left) (\lv -> transE <$> hErr (st z lv)))
         (either (Leaf . EitherL . Left)       (hErr . k))

either :: (v -> c) -> (l a -> c) -> EitherL v l a -> c
either f  _  (EitherL (Left   x))  =  f x
either _  g  (EitherL (Right  y))  =  g y

transE :: EitherL v Id (l a) -> EitherL v l a
transE (EitherL (Left   x))  = EitherL $ Left x
transE (EitherL (Right  y))  = EitherL $ Right $ unId y

err    :: (Failing v :<<: σ) => v -> Tree σ Id a
err x  = Node (injSig (Err x)) (Id ()) (\x _ -> case x of) (\x -> case x of)
