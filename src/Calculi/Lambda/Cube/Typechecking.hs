{-# LANGUAGE FlexibleInstances #-}
{-|
    Module containing typechecking functions and data structures.

-}
module Calculi.Lambda.Cube.Typechecking (
    -- * Typeclasses for Typechecking and Inference
      Typecheckable(..)
    , Inferable(..)
    -- * Typing context and Type error structures
    -- ** General use
    , Typecheck
    , runTypecheck
    , ErrorContext(..)
    , expression
    , environment
    , errorOfContext
    , ErrorContext'
    -- ** Simply-typed lambda calculus
    , SimpleTypingContext(..)
    , NotKnownErr(..)
    , SimpleTypeErr(..)
    -- ** Polymorphic types
    , SubsErr(..)
    , ConflictTree
    -- * Type Helpers
    , (:+:)
) where


import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Data.Bifunctor
import           Control.Monad.State
import           Control.Monad.Except
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified Data.List.NonEmpty  as NE
import           Control.Lens
import           Data.Tree           as Tree

{-|
    Data type for an error context, holding the expression where
    the error occurred, the environment when it did, and the error
    itself.
-}
data ErrorContext env v t err = ErrorContext {
      _expression     :: [LambdaExpr v t]
      -- ^ A stack of expressions leading the the expression that
      -- caused the error as the final element.
    , _environment    :: env
      -- ^ The environment's state at the time of error.
    , _errorOfContext :: err
      -- ^ The error that occurred.
} deriving (Eq, Ord, Show)

makeLenses ''ErrorContext

{-|
    ErrorContext but the environment is assumed to be the TypingContext of @t@.
-}
type ErrorContext' v t err = ErrorContext (TypingContext v t) v t err

instance Functor (ErrorContext env v t) where
    fmap f = errorOfContext %~ f

{-|
    Name-related errors, for when there's a variable, type or constant
    that doesn't appear in the environment that was given to the typechecker.
-}
data NotKnownErr v t =
      UnknownType t
    -- ^ A type appears that is not in scope
    | UnknownVariable v
    -- ^ A variable appears that is not in scope
    deriving (Eq, Ord, Show)

data SimpleTypeErr t =
      NotAFunction t
    -- ^ Attempted to split a type (a -> b) into (Just (a, b)), but the type wasn't
    -- a function type.
    | UnexpectedType t t
    -- ^ The first type was expected during typechecking, but the second type was found.
    deriving (Eq, Ord, Show)

{-|
    A substitution clash's root, with a tree of types substituting
    variables as the first element [1] and the second element being the
    type where these clashing substitutions converge.

    [1]: to be read that the first element of the tuple is a forest of
    substitutions leading the final type (the second element), and
    because of their convergence the first layer of the trees should
    all be substituting the same variable.
-}
type ConflictTree t p = ([Tree (t, [p])], t)

{-|
    Typechecking type, uses the TypingContext as state and TypeError as an exception type.
-}
type Typecheck v t = ExceptT [TypeError v t] (State (TypingContext v t))

-- | runs a Typecheck action
runTypecheck :: st -> ExceptT e (State st) t -> Either e (st, t)
runTypecheck env = (\(e, st) -> (,) st <$> e ) . flip runState env . runExceptT

{-|
    Errors in type variable/poly type substitution.
-}
data SubsErr gr t p =
      MultipleSubstitutions (ConflictTree t p)
    -- ^ There are multiple possible substitutions, the first argument here
    -- is the type that has multiple substitutions and the second is the
    -- list of all the conflicting substitutions' paths.
    | CyclicSubstitution (gr t p)
    -- ^ There is a cycle of substitutions.
    | SubsMismatch t t
    -- ^ A substitution between two incompatable type expressions
    -- was attempted. (i.e. @`substitutions` (X) (Y → Y)@)
    deriving (Eq, Show, Read)

{-|
    Infix `Either`
-}
type (:+:) = Either

infixr 1 :+:

class SimpleType t => Typecheckable v t where
    {-|
        The typing context, in type theory this is usually denoted as 𝚪.

        For a basic typechecker of the simply-typed lambda calculus this might contain
        a mapping of variable names to their types. This is left to be defined
        for the implementer though as other typesystems might need extra information
        in their contexts.
    -}
    type TypingContext v t :: *

    {-|
        The type error representation.
    -}
    type TypeError v t :: *

    {-|
        Given a typing context, typecheck an expression and either return a typeerror or the
        type of the expression that was passed.
    -}
    typecheck :: TypingContext v t             -- ^ The given context
              -> LambdaExpr v t                -- ^ The expression to typecheck
              -> Either [TypeError v t]
                        (TypingContext v t, t) -- ^ The result

class (Typecheckable v t) => Inferable v t where

    {-|
        The inference context, has a similar function to `TypingContext`
    -}
    type InferenceContext v t :: *

    {-|
        The inference error representation.
    -}
    type InferError v t :: *

    infer :: InferenceContext v t                          -- ^ The given context
          -> LambdaExpr v (Maybe t)                        -- ^ The expression to infer from
          -> Either (InferError v t)
                    (InferenceContext v t, LambdaExpr v t) -- ^ The result
