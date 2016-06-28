module Calculi.Lambda.Cube.Dependent where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType

{-|
    Typesystems which can
-}
class SimpleType t => Dependent t where

    -- | The variable type to be used
    type VarType t :: *

    {-|
        Lift a value to a type.
    -}
    valueToType :: LambdaExpr (VarType t) t -> t
