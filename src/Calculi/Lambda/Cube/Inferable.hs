{-|
    Module describing a typeclass for inferability for a system-f
    (higher-order polymorphic lambda calculus) compatable types.
-}
module Calculi.Lambda.Cube.Inferable where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import qualified Control.Monad.State.Lazy        as State
import qualified Data.Map                        as Map
import qualified Data.Set                        as Set
