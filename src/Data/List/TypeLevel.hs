{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Data.List.TypeLevel where

type family (++) (xs :: [a]) (ys :: [a]) :: [a] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys) 
