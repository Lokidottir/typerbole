{-|
    Re-export of the type expression AST exposed by TemplateHaskell with instances
    of `SimpleType`, `HigherOrder`, and `Polymorphic`.
-}
module Compiler.Typesystem.Hask (
      Type(..)
    , Name(..)
) where

import Language.Haskell.TH.Syntax as TH (Type(..), Name(..), TyVarBndr(..))
import Calculi.Lambda.Cube.HigherOrder
import Calculi.Lambda.Cube.Polymorphic
import Calculi.Lambda.Cube.SimpleType
import Calculi.Lambda.Cube.Typechecking
import qualified Data.Set as Set
import Data.Semigroup

instance SimpleType Type where

    type MonoType Type = Name

    abstract a b = (ArrowT `AppT` a) `AppT` b

    reify ((ArrowT `AppT` a) `AppT` b) = Just (a, b)
    reify _ = Nothing

    mono = ConT

    bases = \case
        ForallT binds _ texpr -> bases texpr
        AppT arg ret          -> bases arg <> bases ret
        SigT texpr _          -> bases texpr
        a                     -> Set.singleton a

    equivalent = areAlphaEquivalent

instance Polymorphic Type where

    type PolyType Type = Name

    substitutions = curry $ \case
        (ForallT _ _ texpr1, texpr2)             -> substitutions texpr1 texpr2
        (texpr1            , ForallT _ _ texpr2) -> substitutions texpr1 texpr2
        (SigT texpr1 _     , texpr2)             -> substitutions texpr1 texpr2
        (texpr1            , SigT texpr2 _)      -> substitutions texpr1 texpr2
        (VarT v1           , VarT v2)            -> Right [Mutual v1 v2]
        (VarT v            , texpr)              -> Right [Substitution texpr v]
        (texpr             , VarT v)             -> Right [Substitution texpr v]
        (AppT arg1 ret1    , AppT arg2 ret2)     -> substitutions arg1 arg2 <><> substitutions ret1 ret2
        (texpr1            , texpr2)
            | texpr1 == texpr2 -> Right []
            | otherwise        -> Left [(texpr1, texpr2)]
