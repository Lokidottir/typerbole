module Calculi.Lambda.Cube.Dependent where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType

{-|
    Typesystems which can have values at the type-level.
-}
class SimpleType t => Dependent t where

    {-|
        The type representing value-level variables at the type level.
    -}
    type DependentVariable t :: *

    {-|
        The type representing value-level constants at the type level.
    -}
    type DependentConstant t :: *

    {-|
        Encode a value at the type-level. This could be just a constructor or
        a complete transformation of the AST, but this typeclass doesn't care.
    -}
    valueToType :: LambdaTerm (DependentConstant t) (DependentVariable t) t -> t
