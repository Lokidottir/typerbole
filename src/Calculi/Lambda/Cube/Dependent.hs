module Calculi.Lambda.Cube.Dependent where

import Calculi.Lambda.Cube.SimpleType

{-|
    Typesystems which can have values in their types.
-}
class SimpleType t => Dependent t where
    
    {-|
        A value-level term that can be encoded as a type expression.

        Of kind @* -> *@ because it expects a typesystem as a parameter.
    -}
    type DependentTerm t :: * -> *

    {-|
        Encode a value at the type-level. This could be just a constructor or
        a complete transformation of the AST, but this typeclass doesn't care.
    -}
    valueToType :: (DependentTerm t) t -> t
