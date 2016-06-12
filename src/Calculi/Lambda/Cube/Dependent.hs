module Calculi.Lambda.Cube.Dependent where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType

{-|
    Dependent types, scary things. Very scary things. Not yet implemented.
-}
class SimpleType t => Dependent t where
    -- Going to want to have a method for exposing values to
    -- the type expression.
