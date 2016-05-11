{-|
    Module containing typechecking functions and data structures.

    The code for this is currently commented out, as this is beyond the current
    scope at this time.
-}
module Calculi.Lambda.Cube.Typechecking (
) where

{-
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
