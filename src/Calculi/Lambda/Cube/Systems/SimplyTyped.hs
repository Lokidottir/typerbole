{-# LANGUAGE LambdaCase #-}
module Calculi.Lambda.Cube.Systems.SimplyTyped where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import qualified Data.Map                       as Map
import qualified Data.Set                       as Set

{-|
    Data type describing a type system for simply-typed lambda calculus (λ→).
-}
data SimplyTyped t =
      Mono t
    | Function (SimplyTyped t) (SimplyTyped t)
    deriving (Show, Read, Eq, Ord)

instance Functor SimplyTyped where
    fmap f = \case
        Mono t -> Mono (f t)
        Function t1 t2 -> Function (fmap f t1) (fmap f t2)

instance Foldable SimplyTyped where
    foldr f z = \case
        Mono t -> f t z
        Function t1 t2 -> foldr f (foldr f z t2) t1

instance Ord t => SimpleType (SimplyTyped t) where
    abstract = Function

    reify (Function x y) = Just (x, y)
    reify _              = Nothing

    bases (Mono t)         = Set.singleton (Mono t)
    bases (Function t1 t2) = bases t1 `Set.union` bases t2
