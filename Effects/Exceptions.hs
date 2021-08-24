{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Effects.Exceptions where

import Prelude hiding (either)

import General

data Throwing x v :: * -> (* -> *) -> * where
  Throw  :: x ->  Throwing x v Void  NoSub
  Catch  ::       Throwing x v v     (MaybeSub x v)

hExc  :: (Functor l)
      => Tree (Throwing x v :++: σ) l a
      -> Tree σ (EitherL (l (), x) l) (EitherL (l (), x) Id a)
hExc (Leaf x)                           = Leaf $ EitherL $ Right $ Id x
hExc (Node (Inl' (Throw x))  l  _   _)  = Leaf $ EitherL $ Left (l, x)
hExc (Node (Inl' Catch)      l  st  k)  = hExc (st NothingS l)
  >>= either (\(l', x) -> hExc (st (JustS x) l')
                        >>= either (Leaf . EitherL . Left) (hExc . k . unId))
            (hExc . k . unId)
hExc (Node (Inr' c)          l  st  k)  =
  Node c  (EitherL $ Right l)
          (\z -> either  (Leaf . EitherL . Left)
                         (\lv -> transE <$> hExc (st z lv)))
          (either (Leaf . EitherL . Left) (hExc . k))

either :: (v -> c) -> (l a -> c) -> EitherL v l a -> c
either f  _  (EitherL (Left   x))  =  f x
either _  g  (EitherL (Right  y))  =  g y

transE :: EitherL v Id (l a) -> EitherL v l a
transE (EitherL (Left   x))  = EitherL $ Left x
transE (EitherL (Right  y))  = EitherL $ Right $ unId y

throw      :: forall x v σ . (Throwing x v :<<: σ) => x -> Tree σ Id v
throw e    = Node  (injSig (Throw e :: Throwing x v Void NoSub))
                   (Id ())
                   (\x _ -> case x of)
                   (\x -> case x of)

catch      :: forall x v σ . (Throwing x v :<<: σ)
           => Tree σ Id v -> (x -> Tree σ Id v) -> Tree σ Id v
catch p h  = Node  (injSig (Catch :: Throwing x v v (MaybeSub x v)))
                   (Id ())
                   (\z _ -> case z of
                    JustS x   -> Id <$> (h x)
                    NothingS  -> Id <$> p)
                   (Leaf . unId)
