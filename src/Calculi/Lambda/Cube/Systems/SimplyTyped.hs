module Calculi.Lambda.Cube.Systems.SimplyTyped where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import qualified Control.Monad.State            as State
import           Data.Generics
import qualified Data.Map                       as Map
import           Data.Random.Generics
import qualified Data.Set                       as Set
import           Test.QuickCheck
import qualified Language.Haskell.TH.Lift as TH

{-|
    Data type describing a type system for simply-typed lambda calculus (λ→).
-}
data SimplyTyped t =
      Mono t
    | Function (SimplyTyped t) (SimplyTyped t)
    deriving (Show, Read, Eq, Ord, Data)

TH.deriveLift ''SimplyTyped

instance Functor SimplyTyped where
    fmap f = \case
        Mono t -> Mono (f t)
        Function t1 t2 -> Function (fmap f t1) (fmap f t2)

instance Foldable SimplyTyped where
    foldr f z = \case
        Mono t -> f t z
        Function t1 t2 -> foldr f (foldr f z t2) t1

instance Ord t => SimpleType (SimplyTyped t) where
    type MonoType (SimplyTyped t) = t

    abstract = Function

    reify (Function x y) = Just (x, y)
    reify _              = Nothing

    bases (Mono t)         = Set.singleton (Mono t)
    bases (Function t1 t2) = bases t1 `Set.union` bases t2

    mono = Mono

instance (Data t, Arbitrary t) => Arbitrary (SimplyTyped t) where
    -- TODO: remove instance of Data for t
    arbitrary = sized generatorP
