{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Compiler.Typesystem.SimplyTyped where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Typechecking
import           Control.Monad
import qualified Control.Monad.State            as State
import           Data.Bifunctor
import           Data.Generics
import qualified Data.Map                       as Map
import           Data.Random.Generics
import           Data.Semigroup
import qualified Data.Set                       as Set
import           Test.QuickCheck
import qualified Language.Haskell.TH.Lift as TH

{-|
    Data type describing a type system for simply-typed lambda calculus (λ→).
-}
data SimplyTyped m =
      Mono m
    | Function (SimplyTyped m) (SimplyTyped m)
    deriving (Show, Read, Eq, Ord, Data)

TH.deriveLift ''SimplyTyped

instance Functor SimplyTyped where
    fmap f = \case
        Mono m -> Mono (f m)
        Function from to -> Function (fmap f from) (fmap f to)

instance Foldable SimplyTyped where
    foldr f z = \case
        Mono m -> f m z
        Function from to -> foldr f (foldr f z to) from

instance Ord m => SimpleType (SimplyTyped m) where
    type MonoType (SimplyTyped m) = m

    abstract = Function

    reify (Function from to) = Just (from, to)
    reify _                  = Nothing

    bases (Mono m)           = Set.singleton (Mono m)
    bases (Function from to) = bases from `Set.union` bases to

    mono = Mono

    equivalent = (==)

data SimplyTypedErr c v t =
      STNotKnownErr (NotKnownErr c v t)
    | STSimpleTypeErr (SimpleTypeErr t)
    deriving (Eq, Ord, Show)

instance (Ord m, Ord c, Ord v) => Typecheckable (LambdaTerm c v) (SimplyTyped m) where
    type TypingContext (LambdaTerm c v) (SimplyTyped m) = (SimpleTypingContext c v (SimplyTyped m))

    type TypeError (LambdaTerm c v) (SimplyTyped m) =
        -- Using an ErrorContext because it can hold a lot of information.
        ErrorContext'
            (LambdaTerm c v)
            (SimplyTyped m) (SimplyTypedErr c v (SimplyTyped m))

    typecheck env _expr =
        -- Always add the current expression to all the errors that have occurred
        -- so there's a list of expressions towards the error that happened.
        first (fmap (\err -> err { _expression = _expr : _expression err }))
        $ case _expr of
            {-
                Case of a LC variable, not really typechecking but instead
                checking that the variable name is in scope.
            -}
            Variable v ->
                let -- If there's an error on the var lookup, return this as the error.
                    err = Left [ErrorContext [] env (STNotKnownErr (UnknownVariable v))]
                    -- If it succeeds in it's lookup, pipe the result into a tuple in a Right value.
                    success = (Right . (,) env)
                in maybe err success (Map.lookup v (_variables env))

            {-
                Application of two expressions.
            -}
            (Apply fun arg) ->
                let -- Typecheck both the function side and the argument
                    fun' = typecheck env fun
                    arg' = typecheck env arg
                in case (fun', arg') of
                    -- If both errored, then combine the errors.
                    (Left fun'err, Left arg'err) -> Left $ fun'err <> arg'err
                    _ -> do
                        -- discard their contexts
                        (_, fun'type) <- fun'
                        (_, arg'type) <- arg'
                        case reify fun'type of
                            Nothing       ->
                                -- The first expression's type wasn't a function type.
                                Left [ErrorContext [fun] env (STSimpleTypeErr $ NotAFunction fun'type)]
                            Just (funarg'type, funret'type)
                                | funarg'type /= arg'type ->
                                    -- The type of the argument expression doesn't match the expected
                                    -- type of the function expression.
                                    Left [ErrorContext [fun] env (STSimpleTypeErr $ UnexpectedType funarg'type arg'type)]
                                | otherwise ->
                                    -- succeeded in typechecking.
                                    Right (env, funret'type)

            {-
                Abstracting a variable over an expression.
            -}
            (Lambda (var, var'type) expr) -> do
                -- Get any types in var'type not in the set of all types
                -- as every type should be declared by the environment
                -- before appearing in an expression.
                let unknownTypes = Set.toList $ Set.difference (bases var'type) (_allTypes env)
                let errFun t = ErrorContext [] env (STNotKnownErr$ UnknownType t)
                -- If there are unknown types, error on them.
                unless (null unknownTypes) . Left $ errFun <$> unknownTypes
                -- If we get ths far, then var'type was valid
                -- Set a new typing context with var brought into scope
                let env' = env { _variables = Map.insert var var'type (_variables env) }
                -- Typecheck the lambda's body
                (_, expr'type) <- typecheck env' expr
                -- Return the environment and the type of the lambda expression.
                return (env, var'type /-> expr'type)

instance (Data m, Arbitrary m) => Arbitrary (SimplyTyped m) where
    arbitrary = sized $ generatorPWith [alias (\() -> arbitrary :: Gen m)]
