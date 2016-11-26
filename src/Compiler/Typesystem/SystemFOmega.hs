{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-|
    <https://en.wikipedia.org/wiki/System_F#System_F.CF.89 System Fω> is a System F that allows
    type operators (@Set Int@, @List Int@, @Either Int Bool@ etc.)
-}
module Compiler.Typesystem.SystemFOmega (
      SystemFOmega
    , markAsFunctionArrow
) where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import           Control.Typecheckable
import           Compiler.Typesystem.SimplyTyped (SimplyTyped)
import qualified Language.Haskell.TH.Lift as TH
import           Data.Bifunctor.TH
import           Data.Generics
import           Generic.Random.Data
import           Data.Semigroup
import qualified Data.Set                        as Set
import           Test.QuickCheck

{-|
    A data type representing the components of System-Fω, with a parameterized
    higher-order typesystem @k@.
-}
data SystemFOmega m p k =
      Mono m
      -- ^ A mono type
    | FunctionArrow
      -- ^ Explicitly stated mono type of kind @(* → * → *)@ for type application reasons
    | Poly p
      -- ^ A poly type, i.e. the "@a@" in "@∀ a. a → a@"
    | Forall (p, k) (SystemFOmega m p k)
      -- ^ A binding of a poly type in a type expression, i.e. the "@∀ a.@" in "@∀ a. a@"
    | TypeAp (SystemFOmega m p k) (SystemFOmega m p k)
      -- ^ Type application.
    deriving (Eq, Ord, Show, Read, Data)

infixl 0 `TypeAp`

deriveBifunctor ''SystemFOmega
deriveBifoldable ''SystemFOmega
deriveBitraversable ''SystemFOmega
TH.deriveLift ''SystemFOmega

instance (Data m, Data p, Data k, Arbitrary m, Arbitrary p, Arbitrary k) => Arbitrary (SystemFOmega m p k) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized (generatorSRWith aliases) where
        aliases :: [AliasR Gen]
        aliases = [
                    aliasR (\() -> arbitrary :: Gen m)
                  , aliasR (\() -> arbitrary :: Gen p)
                  ]

{-|
    Given a function arrow representation of type @m@, replace all
    matching mono types with the function arrow.
-}
markAsFunctionArrow :: Eq m => m -> SystemFOmega m p k -> SystemFOmega m p k
markAsFunctionArrow sub = \case
    m@(Mono x)
        | x == sub -> FunctionArrow
        | otherwise -> m
    FunctionArrow -> FunctionArrow
    p@Poly{} -> p
    Forall p st -> Forall p (markAsFunctionArrow sub st)
    TypeAp t1 t2 -> TypeAp (markAsFunctionArrow sub t1) (markAsFunctionArrow sub t2)
