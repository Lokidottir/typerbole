module Calculi.Lambda.Cube.Dependent where

import Calculi.Lambda.Cube.SimpleType

{-|
    Typesystems which can have values (@term@) in their types (@t@).
-}
class SimpleType t => Dependent term t where

    {-|
        Encode a value at the type-level. This could be just a constructor or
        a complete transformation of the AST, but this typeclass doesn't care.
    -}
    valueToType :: term t -> t
