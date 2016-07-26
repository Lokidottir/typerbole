{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
    Module containing typechecking functions and data structures.

-}
module Control.Typecheckable (
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
) where

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
type ErrorContext' term t err = ErrorContext (TypingContext term t) (term t) err

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
    Typechecking type, uses the TypingContext as state and TypeError as an exception type.
-}
type Typecheck term t = ExceptT [TypeError term t] (State (TypingContext term t))

-- | runs a `Typecheck` action
runTypecheck :: st -> ExceptT e (State st) t -> Either e (st, t)
runTypecheck env = (\(e, st) -> (,) st <$> e ) . flip runState env . runExceptT

{-|
    A typeclass for typechecking terms (@term@) with a typesystem (@t@).
-}
class Typecheckable (term :: * -> *) t where
    {-|
        The typing context, in type theory this is usually shown as 𝚪.

        For a basic typechecker of the simply-typed lambda calculus this might contain
        a mapping of variable and constant names to their types. This is left to be defined
        for the implementer though as other typesystems might need extra information
        in their contexts.
    -}
    type TypingContext term t :: *

    {-|
        The type error representation.
    -}
    type TypeError term t :: *

    {-|
        Given a typing context, typecheck an expression and either return a typeerror or the
        type of the expression that was passed.
    -}
    typecheck :: TypingContext term t            -- ^ The given context
              -> term t                          -- ^ The expression to typecheck
              -> Either [TypeError term t]
                        (TypingContext term t, t) -- ^ The result

class (Typecheckable term t) => Inferable term t where

    {-|
        The inference context, has a similar function to `TypingContext`
    -}
    type InferenceContext term t :: *

    {-|
        The inference error representation.
    -}
    type InferError term t :: *

    infer :: InferenceContext term t                  -- ^ The given context
          -> term (Maybe t)                           -- ^ The expression to infer from
          -> Either [InferError term t]
                    (TypingContext term t, term t) -- ^ The result
