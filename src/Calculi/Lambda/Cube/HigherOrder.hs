{-# LANGUAGE FlexibleContexts #-}
module Calculi.Lambda.Cube.HigherOrder where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Typechecking
import qualified Data.Map                                as Map

type KindEnvironment t = Map.Map t (Kindedness t)

{-|
    The type constants for higher-order typed lambda calculus.
-}
data Star =
      Star
    -- ^ The kind constant "@*@".
    deriving (Eq, Ord, Show, Read)

{-|
    The representation to be typechecked at the kind level.
-}
type Kindedness t = LambdaTerm t () (Kindsystem t)

{-|
    Typeclass for higher-order types.
-}
class (Typecheckable t () (Kindsystem t), SimpleType t) => HigherOrder t where
    {-|
        The typesystem of the typesystem.
    -}
    type Kindsystem t :: *

    {-|
        Turn a type expression into a lambda expression describing how the types
        are applied to eachother.
    -}
    kind :: t -> Kindedness t

    {-|
        More generalised form of `abstract` to work on all type operators, not
        just function types.

        @`typeap` M (∀a. a) = (∀ a. M a)@

        @`typeap` T X       = (T X)@

        @`typeap` (`typeap` ((→)) A) B ≡ `abstract` A B@
    -}
    typeap :: t -> t -> t

    {-|
        More generalised form of `reify`, working on all type application.

        @`untypeap` (M x)   = Just (M, x)@

        @`untypeap` (X → Y) = Just (((→) X), Y)@

        @`untypeap` X       = Nothing@
    -}
    untypeap :: t -> Maybe (t, t)

{-|
    Typecheck a type expression's kindedness.
-}
kindcheck :: forall t ksys. (Kindsystem t ~ ksys, HigherOrder t)
          => TypingContext t () ksys                -- ^ A typing context for typechecking
          -> t                                      -- ^ A type expression to kindcheck
          -> Either [TypeError t () ksys]
                    (TypingContext t () ksys, ksys) -- ^ The result.
kindcheck ctx texpr = typecheck ctx (kind texpr)

{-|
    Infix `typeap`.
-}
(/$) :: (HigherOrder t) => t -> t -> t
(/$) = typeap
infixl 8 /$

{-|
    Shorthand for the constant `Star` in typesystems.
-}
star :: (SimpleType t, MonoType t ~ Star) => t
star = mono Star
