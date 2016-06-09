{-# LANGUAGE FlexibleInstances #-}
module Calculi.Lambda.Cube.Systems.SimplyTyped where

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
data SimplyTyped t =
      Mono t
    | Function (SimplyTyped t) (SimplyTyped t)
    deriving (Show, Read, Eq, Ord, Data)

TH.deriveLift ''SimplyTyped

instance Functor SimplyTyped where
    fmap f = \case
        Mono t -> Mono (f t)
        Function t1 t2 -> Function (fmap f t1) (fmap f t2)

instance Foldable SimplyTyped where
    foldr f z = \case
        Mono t -> f t z
        Function t1 t2 -> foldr f (foldr f z t2) t1

instance Ord t => SimpleType (SimplyTyped t) where
    type MonoType (SimplyTyped t) = t

    abstract = Function

    reify (Function x y) = Just (x, y)
    reify _              = Nothing

    bases (Mono t)         = Set.singleton (Mono t)
    bases (Function t1 t2) = bases t1 `Set.union` bases t2

    mono = Mono

instance (Ord v, Ord t) => Typecheckable v (SimplyTyped t) where
    type TypingContext v (SimplyTyped t) = (TypingEnvironment v (SimplyTyped t))

    -- Horrible error wrapper that gives a lot of information.
    type TypeError v (SimplyTyped t) =
        ErrorContext
            TypingEnvironment
            v
            (SimplyTyped t)
            (NotKnownErr v (SimplyTyped t) :+: SimpleTypeErr (SimplyTyped t))

    typecheck env _expr =
        -- Always cons the current expression to all the errors that have occurred
        -- so there's a list of expressions towards the error that happened.
        first (fmap (\err -> err { expression = _expr : expression err }))
        $ case _expr of
            {-
                Case of a LC variable, not really typechecking but instead
                checking that the variable name is in scope.
            -}
            Var v ->
                let -- If there's an error on the var lookup, return this as the error.
                    err = Left [ErrorContext [] env (Left (UnknownVariable v))]
                    -- If it succeeds in it's lookup, pipe the result into a tuple in a Right value.
                    success = (Right . (,) env)
                in maybe err success (Map.lookup v (vars env))

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
                                Left [ErrorContext [fun] env (Right $ NotAFunction fun'type)]
                            Just (funarg'type, funret'type)
                                | funarg'type /= arg'type ->
                                    -- The type of the argument expression doesn't match the expected
                                    -- type of the function expression.
                                    Left [ErrorContext [fun] env (Right $ UnexpectedType funarg'type arg'type)]
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
                let unknownTypes = Set.toList $ Set.difference (bases var'type) (allTypes env)
                let errFun t = ErrorContext [] env (Left $ UnknownType t)
                -- If there are unknown types, error on them.
                unless (null unknownTypes) . Left $ errFun <$> unknownTypes
                -- If we get ths far, then var'type was valid
                -- Set a new typing context with var brought into scope
                let env' = env { vars = Map.insert var var'type (vars env) }
                -- Typecheck the lambda's body
                (_, expr'type) <- typecheck env' expr
                -- Return the environment and the type of the lambda expression.
                return (env, var'type /-> expr'type)

instance (Data t, Arbitrary t) => Arbitrary (SimplyTyped t) where
    -- TODO: remove instance of Data for t
    arbitrary = sized generatorP
