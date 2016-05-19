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

{-
{-|
    Reporter for types and variables that are not in scope.
-}
data NotKnownReporter v t m err = NotKnownReporter {
      typeNotKnown :: t -> LambdaExpr v t -> TypingEnvironment v t -> m (Report v t err)
      -- ^ A type (The first argument) appears that is not in scope.
    , varNotKnown  :: v -> LambdaExpr v t -> TypingEnvironment v t -> m (Report v t err)
      -- ^ A variable or constant's name (the first argument) appears that is not in scope.
}

instance Functor m => Functor (NotKnownReporter v t m) where
    fmap f rep = let f' = fmap (first f) in
        NotKnownReporter (\t lam env -> f' (typeNotKnown rep t lam env))
                         (\v lam env -> f' (varNotKnown  rep v lam env))

{-|
    Reporter for typesystems implementing `SimplyTyped`.
-}
data SimpleTypeReporter v t m err = SimpleTypeReporter {
      mismatchedTypes :: (t, t) -> LambdaExpr v t -> TypingEnvironment v t -> m (Report v t err)
      -- ^ two given types don't match during typechecking, where the first was
      -- found while the second was expected.
    , couldNotReify   :: t -> LambdaExpr v t -> TypingEnvironment v t -> m (Report v t err)
      -- ^ A type was expected to be able to be reified as if it were a function type, but
      -- returned Nothing when it was applied to `Nothing`.
}

instance Functor m => Functor (SimpleTypeReporter v t m) where
    fmap f rep = let f' = fmap (first f) in
        SimpleTypeReporter (\ts lam env -> f' (mismatchedTypes rep ts lam env))
                           (\t  lam env -> f' (couldNotReify   rep t  lam env))
-}
