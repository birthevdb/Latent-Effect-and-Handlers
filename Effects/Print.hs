{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Effects.Print where

import General

data Printing v :: * -> (* -> *) -> * where
  Print :: String -> Printing v v NoSub

hPrint  :: (Functor l, String :<<<: v)
        => Tree (Printing v :++: σ) l a -> Tree σ l a
hPrint (Leaf x)                         = Leaf x
hPrint (Node (Inl' (Print s)) l _   k)  = hPrint (k (const (injV s) <$> l))
hPrint (Node (Inr' c)         l st  k)  = Node c l (\s -> hPrint . st s) (hPrint . k)

print :: (Printing v :<<: σ) => String -> Tree σ Id v
print s = noSubNode (Print s)
