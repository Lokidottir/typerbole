{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Compiler.Typesystem.CalculusOfConstructions where

import           Control.Typecheckable.PureTypecheckable
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Dependent
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Data.List.NonEmpty   (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map   (Map)
import qualified Data.Map as Map

newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance (Eq (f (Fix f))) => Eq (Fix f)
deriving instance (Ord (f (Fix f))) => Ord (Fix f)
deriving instance (Show (f (Fix f))) => Show (Fix f)

-- | A calculus of constructions, with it's fixed point in it's type annotations.
data CalculusOfConstructions c v t =
      Var v
    | Con c
    | Apply (CalculusOfConstructions c v t) (CalculusOfConstructions c v t)
    | Lambda (v, t) (CalculusOfConstructions c v t)
    | Pi (v, t) t
    deriving (Eq, Ord, Show, Functor)

data COCConsts =
      FunctionArrow
    deriving (Eq, Ord, Show)

type WithConsts = Either COCConsts

-- | Type synonym that shortens the name, adds type constants, and makes CoC fixed-point
type CalcOfCons c v = Fix (CalculusOfConstructions (WithConsts c) v)

instance (Ord c, Ord v) => SimpleType (CalcOfCons c v) where

    type TypeConstant (CalcOfCons c v) = WithConsts c

    abstract a b = Fix $ (Con (Left FunctionArrow) `Apply` unFix a) `Apply` unFix b

    typeconst = Fix . Con

    equivalent = (==)

data CoCTypingContext c v = CoCTC {
        cocconsts :: Map c (CalcOfCons c v)
      , cocvars :: Map v (CalcOfCons c v)
    } deriving (Eq, Ord, Show)

instance (Ord c, Ord v) => PureTypecheckable (CalculusOfConstructions (WithConsts c) v) (CalcOfCons c v) where

    type TypeError (CalculusOfConstructions (WithConsts c) v) (CalcOfCons c v) = NonEmpty String

    type TypingContext (CalculusOfConstructions (WithConsts c) v) (CalcOfCons c v) = CoCTypingContext c v
