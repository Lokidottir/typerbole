{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
    , expression
    , environment
    , (<><>)
    -- ** ErrorContext
    , ErrorContext(..)
    , ErrorContext'
    , throwErrorContext
    , throwErrorContexts
    , errorOfContext
    , appendExprToEContexts
    -- ** Simply-typed lambda calculus
    , SimpleTypingContext(..)
    , NotKnownErr(..)
    , SimpleTypeErr(..)
) where


import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Data.Bifunctor
import           Control.Monad.State
import           Control.Monad.Except
import           Data.Semigroup
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
data ErrorContext env expr err = ErrorContext {
      _expression     :: [expr]
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
type ErrorContext' c v t err = ErrorContext (TypingContext c v t) (LambdaTerm c v t) err

instance Functor (ErrorContext env expr) where
    fmap f = errorOfContext %~ f

{-|
    Throw an error in an 'ErrorContext'.
-}
throwErrorContext exprStack err = throwErrorContexts [(exprStack, err)]

{-|
    Throw a list of errors in `ErrorContext`'s.
-}
throwErrorContexts exprsAndErrs = do
    -- Get the current environment at the time of the errors.
    env <- get
    -- For every error, create an ErrorContext with the environment 'env' and the given error
    -- error and expression stack.
    throwError ((\(exprStack, err) -> ErrorContext exprStack env err) <$> exprsAndErrs)

{-|
    If there have been any errors, add the given expression to the head of
    all the error contexts' expression stacks.
-}
appendExprToEContexts expr = flip catchError (throwError . fmap (expression %~ (expr :)))

{-|
    A validation semigroup on Eithers, combining Left values when two appear.
-}
(<><>) :: (Semigroup s1, Semigroup s2) => Either s1 s2 -> Either s1 s2 -> Either s1 s2
(<><>) = curry $ \case
    (Left a, Left b) -> Left (a <> b)
    (a, b)           -> (<>) <$> a <*> b

{-|
    Name-related errors, for when there's a variable, type or constant
    that doesn't appear in the environment that was given to the typechecker.
-}
data NotKnownErr c v t =
      UnknownType t
    -- ^ A type appears that is not in scope
    | UnknownVariable v
    -- ^ A variable appears that is not in scope
    | UnknownConstant c
    -- ^ A constant appears that is not in scope
    deriving (Eq, Ord, Show)

data SimpleTypeErr t =
      NotAFunction t
    -- ^ Attempted to split a type (a -> b) into (Just (a, b)), but the type wasn't
    -- a function type.
    | UnexpectedType t t
    -- ^ The first type was expected during typechecking, but the second type was found.
    deriving (Eq, Ord, Show)

{-|
    Typechecking type, uses the TypingContext as state and TypeError as an exception type.
-}
type Typecheck c v t = ExceptT [TypeError c v t] (State (TypingContext c v t))

-- | runs a `Typecheck` action
runTypecheck :: st -> ExceptT e (State st) t -> Either e (st, t)
runTypecheck env = (\(e, st) -> (,) st <$> e ) . flip runState env . runExceptT

class SimpleType t => Typecheckable c v t where
    {-|
        The typing context, in type theory this is usually shown as 𝚪.

        For a basic typechecker of the simply-typed lambda calculus this might contain
        a mapping of variable and constant names to their types. This is left to be defined
        for the implementer though as other typesystems might need extra information
        in their contexts.
    -}
    type TypingContext c v t :: *

    {-|
        The type error representation.
    -}
    type TypeError c v t :: *

    {-|
        Given a typing context, typecheck an expression and either return a typeerror or the
        type of the expression that was passed.
    -}
    typecheck :: TypingContext c v t           -- ^ The given context
              -> LambdaTerm c v t              -- ^ The expression to typecheck
              -> Either [TypeError c v t]
                        (TypingContext c v t, t) -- ^ The result

class (Typecheckable c v t) => Inferable c v t where

    {-|
        The inference context, has a similar function to `TypingContext`
    -}
    type InferenceContext c v t :: *

    {-|
        The inference error representation.
    -}
    type InferError c v t :: *

    infer :: InferenceContext c v t                          -- ^ The given context
          -> LambdaTerm c v (Maybe t)                        -- ^ The expression to infer from
          -> Either (InferError c v t)
                    (InferenceContext c v t, LambdaTerm c v t) -- ^ The result
