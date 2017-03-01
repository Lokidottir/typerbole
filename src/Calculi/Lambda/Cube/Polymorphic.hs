{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
) where

import           Calculi.Lambda.Cube.SimpleType

{-|
    Class of typesystems that exhibit polymorphism. Expecting OS
-}
class (Ord (TypeVariable t), SimpleType t, Monad m) => Polymorphic t m where

    {-|
        Unify two given type expressions.

        ===Behavior

        *
          Law: A unification function between two terms must produce equivalent expressions
          when applied to the two terms or fail to unify.

            @
            -- Two type expressions ...
            a, b :: t

            -- ... that are not equivalent ...
            a ==== b
            > False

            -- ... are equivalent when unified, or cannot be unified at all.
            (unify a b >>= \u -> u a ==== u b) = (unify a b >> return True)
            @

        *
          Law: equivalent expressions always unify.

            @
            -- Two type expressions ...
            a, b :: t

            -- ... that are equivalent ...
            a ==== b
            > True

            -- ... will always unify.
            (unify a b >>= \u -> u a ==== u b) = (return True)

            -- Additionally: "u a", "u b", "a", and "b" are all equivalent to eachother.
            @
    -}
    unify :: t -> t -> m (t -> t)

    {-|
        The representation of a type variable.
    -}
    type TypeVariable t :: *

    {-|
        Constructor synonym for type variables.
    -}
    typevar :: TypeVariable t -> t
