{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}


module General where

import Control.Monad

-------------------------------
-- Trees and their Instances --
-------------------------------

data Tree (σ :: * -> (* -> *) -> *) (l :: * -> *) a where
  Leaf  ::  a -> Tree σ l a
  Node  ::  σ p c
        ->  l ()
        ->  (forall x. c x -> l () -> Tree σ l (l x))
        ->  (l p -> Tree σ l a)
        ->  Tree σ l a

instance Functor (Tree σ l) where
  fmap = liftM

instance Applicative (Tree σ l) where
  pure   = return
  (<*>)  = ap

instance Monad (Tree σ l) where
  return                 = Leaf
  Leaf x         >>=  f  = f x
  Node c l st k  >>=  f  = Node c l st (\x -> k x >>= f)

--------------------------
-- Datatypes a la Carte --
--------------------------

class v1 :<<<: v2 where
  injV   :: v1 -> v2
  projV  :: v2 -> Maybe v1

infixr :++:

data (σ1 :++: σ2) :: * -> (* -> *) -> * where
  Inl'  :: σ1 p c  -> (σ1 :++: σ2) p c
  Inr'  :: σ2 p c  -> (σ1 :++: σ2) p c

class (σ1 :: * -> (* -> *) -> *) :<<: σ2 where
  injSig :: σ1 p c -> σ2 p c

instance σ :<<: σ where
  injSig = id

instance {-# OVERLAPPABLE #-} σ1 :<<: (σ1 :++: σ2) where
  injSig = Inl'

instance {-# OVERLAPPABLE #-} (σ1 :<<: σ3) => σ1 :<<: (σ2 :++: σ3) where
  injSig = Inr' . injSig

------------------------------------------
-- Other Datatypes and Helper Functions --
------------------------------------------

data Void

newtype Id a = Id { unId :: a } deriving (Functor)

instance Applicative Id where
    pure a         = Id a
    Id f <*> Id x  = Id (f x)

----------------------------
-- Latent Effect Functors --
----------------------------

newtype StateL s l a  = StateL { unStateL :: (s, l a) }
  deriving Show

instance Functor l => Functor (StateL s l) where
  fmap f (StateL (s, la)) = StateL (s, fmap f la)

newtype EitherL left l a = EitherL { unEitherL :: Either left (l a)}


-----------------------------------------------
-- Extracting the Value from the Effect Tree --
-----------------------------------------------

data Voiding :: * -> (* -> *) -> *

hVoid :: Tree Voiding l a -> a
hVoid (Leaf x) = x

-------------------------------
-- Subtrees of the Tree type --
-------------------------------

data NoSub :: * -> * where

data OneSub v  :: * -> * where
  One :: OneSub v v

data MaybeSub x v :: * -> * where
  JustS     :: x ->  MaybeSub x v v
  NothingS  ::       MaybeSub x v v

noSubNode :: forall v σ1 σ2. σ1 :<<: σ2
          => σ1 v NoSub -> Tree σ2 Id v
noSubNode n = Node (injSig n) (Id ()) (\x -> case x of) (Leaf . unId)

oneSubNode :: forall v w σ1 σ2 . σ1 :<<: σ2
           => σ1 w (OneSub v)  -> Tree σ2 Id v -> Tree σ2 Id w
oneSubNode n t = Node (injSig n) (Id ()) (\ One _ -> Id <$> t) (Leaf . unId)
