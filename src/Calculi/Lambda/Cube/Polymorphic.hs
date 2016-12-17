{-# LANGUAGE FlexibleContexts #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
) where

import           Calculi.Lambda.Cube.SimpleType

{-|
    Class of typesystems that exhibit polymorphism.
-}
class (Ord (TypeVariable t), SimpleType t) => Polymorphic t where

    {-|
        The type that reports any possible errors that occur during unification.
    -}
    type UnifyError t :: *

    {-|
        The context for unification, in many typesystems this may be `()` but in others
        it might be information on the kinds of constants or background knowledge related
        to rewriting terms.
    -}
    type UnifyContext t :: *

    {-|
        Unify two given type expressions.

        ===Behavior

        *
          Law: A unification function between two terms must produce equivalent expressions
          when applied to the two terms

            @
            -- Two type expressions ...
            a, b :: t

            -- ... that are not equivalent ...
            a ==== b
            > False

            -- ... are equivalent when unified, or cannot be unified at all.
            case unify a b of
                Left err -> True -- This property doesn't care about failures
                Right u -> u a ==== u b
            > True
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
            case unify a b of
                Left err -> False
                Right u -> u a ==== u b
            > True

            -- Additionally: "u a", "u b", "a", and "b" are all equivalent to eachother.
            @
    -}
    unify :: UnifyContext t -> t -> t -> (UnifyContext t, Either [UnifyError t] (t -> t))

    {-|
        The representation of a type variable.
    -}
    type TypeVariable t :: *

    {-|
        Constructor synonym for type variables.
    -}
    typevar :: TypeVariable t -> t
