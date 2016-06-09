{-|
    Module containing typechecking functions and data structures.

-}
module Calculi.Lambda.Cube.Typechecking where


import           Calculi.Lambda
import           Calculi.Lambda.Cube
import           Data.Bifunctor
import qualified Data.Map            as Map
import qualified Data.Set            as Set

{-|
    The type of a report, with Left values being an error and Right values
    being a rewrite to replace the lambda expression that generated the error.

    Note that infinite-loops caused by returning an expression with the same problem
    as the lambda expression that was first checked are not currently detected. This
    may change in the future.
-}
type Report v t err = Either err (LambdaExpr v t)

{-|
    Data type for an error context, holding the expression where
    the error occurred, the environment when it did, and the error
    itself.
-}
data ErrorContext env v t err = ErrorContext {
      expression     :: LambdaExpr v t
    , environment    :: env v t
    , errorOfContext :: err
} deriving (Eq, Ord, Show)

instance Functor (ErrorContext env v t) where
    fmap f errctx = errctx { errorOfContext = f (errorOfContext errctx) }

data NotKnownErr v t =
      UnknownType v
    -- ^ A type appears that is not in scope
    | UnknownVariable t
    -- ^ A variable appears that is not in scope
    deriving (Eq, Ord, Show)

data SimpleTypeErr t =
      NotAFunction t
    -- ^ Attempted to split a type (a -> b) into (Just (a, b)), but the type wasn't
    -- a function type.
    | UnexpectedType t t
    -- ^ The first type was expected during typechecking, but the second type was found.
    deriving (Eq, Ord, Show)
