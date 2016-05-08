{-|
    Module describing a typeclass for inferability for a system-f
    (higher-order polymorphic lambda calculus) compatable types.
-}
module Calculi.Lambda.Cube.Inferable where

import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import qualified Data.Set                        as Set

class (Polymorphic t, HigherOrder t) => HMInferable t where
    {-|
        Function retrives all the free type variables (hence "ftvs") in a type.
        If the type is itself an unbound poly type, then that is returned.

        @`ftvs` (∀ a. (∀ b. a → b → c d)) = `Set.fromList` [c, d]@

        @`ftvs` (a → b → c) = `Set.fromList` [a, b, c]@

        @`ftvs` (∀ c. X → c) = `Set.empty`@
    -}
    ftvs :: t -> Set.Set t

    {-|
        Given a typing environment, generate an infinite list of unique poly types
        that do not exist within the given environment.
    -}
    nptTape :: TypingEnvironment v t -> [t]
