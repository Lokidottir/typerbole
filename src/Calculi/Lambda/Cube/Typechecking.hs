{-|
    Module containing typechecking functions and data structures.

-}
module Calculi.Lambda.Cube.Typechecking (
    -- * Typeclasses for Typechecking
      Typecheckable(..)
    , Inferable(..)
    -- * Error Reporting Helper Structures
    , ErrorContext(..)
    -- ** Simply-typed lambda calculus
    , NotKnownErr(..)
    , SimpleTypeErr(..)
    -- ** Polymorphic types
    , SubsErr(..)
    , ClashTreeRoot
) where


import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Data.Bifunctor
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified Data.List.NonEmpty  as NE
import           Data.Tree           as Tree

{-|
    Data type for an error context, holding the expression where
    the error occurred, the environment when it did, and the error
    itself.
-}
data ErrorContext env v t err = ErrorContext {
      expression     :: [LambdaExpr v t]
    , environment    :: env v t
    , errorOfContext :: err
} deriving (Eq, Ord, Show)

instance Functor (ErrorContext env v t) where
    fmap f errctx = errctx { errorOfContext = f (errorOfContext errctx) }

{-|
    Name-related errors, for when there's a variable, type or constant
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
type ClashTreeRoot t p = ([Tree (t, [p])], t)

data SubsErr gr t p =
      MultipleSubstitutions (ClashTreeRoot t p)
    -- ^ There are multiple possible substitutions, the first argument here
    -- is the type that has multiple substitutions and the second is the
    -- list of all the conflicting substitutions' paths.
    | CyclicSubstitution (gr t p)
    -- ^ There is a cycle of
    deriving (Eq, Show, Read)

class SimpleType t => Typecheckable t where
    {-|
        The typing context, in type theory this is usually denoted as 𝚪.

        For a basic typechecker of the simply-typed lambda calculus this might contain
        a mapping of variable names to their types. This is left to be defined
        for the implementer though as other typesystems might need extra information
        in their contexts.
    -}
    type TypingContext t :: *

    {-|
        The type error representation.
    -}
    type TypeError t :: *

    {-|
        Given a typing context, typecheck an expression and either return a typeerror or the
        type of the expression that was passed.
    -}
    typecheck :: Ord v
              => TypingContext t             -- ^ The given context
              -> LambdaExpr v t              -- ^ The expression to typecheck
              -> Either (TypeError t)
                        (TypingContext t, t) -- ^ The result

class (Typecheckable t) => Inferable t where

    {-|
        The inference context, has a similar function to `TypingContext`
    -}
    type InferenceContext t :: *

    {-|
        The inference error representation.
    -}
    type InferError t :: *

    infer :: Ord v
          => InferenceContext t                          -- ^ The given context 
          -> LambdaExpr v (Maybe t)                      -- ^ The expression to infer from
          -> Either (InferError t)
                    (InferenceContext t, LambdaExpr v t) -- ^ The result
