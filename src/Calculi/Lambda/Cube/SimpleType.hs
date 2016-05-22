{-|
    Module describing a typeclass for types with stronger mathematical foundations that
    represents a type system for simply-typed lambda calculus (λ→ on the lambda cube).
-}
module Calculi.Lambda.Cube.SimpleType (
    -- * Typeclass for λ→
      SimpleType(..)
    -- ** Notation and related functions
    , (/->)
    , order
    -- * Typechecking
    , TypingEnvironment(..)
    , typecheckSTLC
    -- ** Type error reporting
    , STReporter(..)
    , stockSTReporter
    , defaultSTReporter
    -- * Other functions
    , prettyprintST
    , isFunction
    , isBase
    , basesOfExpr
    , envFromExpr
) where

import           Calculi.Lambda
import           Control.Monad
import           Data.Bifoldable
import           Data.List
import qualified Data.Map        as Map
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set        as Set
import           Test.QuickCheck

data TypingEnvironment v t = TypingEnvironment {
      vars     :: Map.Map v t
    , allTypes :: Set.Set t
} deriving (Show, Read, Eq, Ord)

{-|
    Typeclass based off simply-typed lambda calculus + a method for getting all
    the base types in a type.
-}
class (Ord t) => SimpleType t where
    {-|
        The representation of a Mono type, also sometimes referred to a type constant.

        in the type expression @A → M@, both @A@ and @M@ are mono types, but in a polymorphic
        type expression such as @∀ a. a → X@, @a@ is not a mono type.
    -}
    type MonoType t :: *

    {-|
        Given two types, generate a new type representing the type of a function from
        the first type to the second.

        @`abstract` K D = (K → D)@

        When polymorphism is present:

        @`abstract` (∀ a. a) T = (∀ a. a → T)@

        @`abstract` a t = (a → t)@
    -}
    abstract :: t -> t -> t

    {-|
        Given a function type, decompose it into it's argument and return types. Effectively
        the inverse of `abstract` but returns `Nothing` when the type isn't a function type.

        @`reify` (K → D) = Just (K, D) @

        @`reify` (K) = Nothing@

        When polymorphism is present:

        @`reify` (∀ a. a → T) = Just (∀ a. a, t)@

        @`reify` (a → T) = Just (a, t)@

        `reify` is almost the inverse of `abstract`, and the following property should hold true:

        prop> fmap (uncurry abstract) (reify t) = Just t

    -}
    reify :: t -> Maybe (t, t)

    {-|
        Given a type, return a set of all the base types that occur within the type.

        @`bases` (∀ a. a) = Set.singleton (a)@

        @`bases` (M X → (X → Z) → M Z) = Set.fromList [M, X, Z] -- or Set.fromList [M, X, Z, →], depending@
    -}
    bases :: t -> Set.Set t

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Mono m".
    -}
    mono :: MonoType t -> t

{-|
    Infix `abstract` with the appearence of @↦@, which is used to denote function
    types in much of mathematics.
-}
(/->) :: SimpleType t => t -> t -> t
(/->) = abstract

infixr 7 /->

{-|
    Find the depth of a type.

    @`order` (M → X) = 1@

    @`order` ((M → Y) → X) = 2@

    @`order` (M → ((Y → Q) → Z) → X) = 2@

    @`order` X = 0@
-}
order :: SimpleType t => t -> Integer
order t = case reify t of
    Nothing -> 0
    Just (t1, t2) -> max (1 + order t1) (order t2)

{-|
    A data type used to report errors during typechecking & inference.

    TODO: Maybe make a version of this that works with rewriting expressions
          and effects by putting this in a (m (Either err (LambdaExpr v t)))
          This might be easier by putting together a typechecking effect/monad
          transformer.
-}
data STReporter v t err = STReporter {
      unknownType     :: t -> LambdaExpr v t -> TypingEnvironment v t -> err
      -- ^ A type is present in an expression which doesn't
      -- appear in the typing environment given.
    , unknownVariable :: v -> LambdaExpr v t -> TypingEnvironment v t -> err
      -- ^ A variable is present that isn't in the typing environment
    , typesDontMatch  :: t -> t -> LambdaExpr v t -> TypingEnvironment v t -> err
      -- ^ two given types don't match during typechecking, where the first was
      -- found while the second was expected.
    , notAFunction    :: t -> LambdaExpr v t -> TypingEnvironment v t -> err
      -- ^ A given type is used in a way that implies it's a function,
      -- but the environment or inference suggests otherwise.
    , cyclicLet       :: [LetDeclr v t] -> LambdaExpr v t -> TypingEnvironment v t -> err
      -- ^ Applicable to simply-typed lambda-calculus only, a let expression
      -- has a cycle, something that isn't a legal structure in STLC.
}

instance Functor (STReporter v t) where
    fmap f rep = STReporter (\t lam env -> f (unknownType rep t lam env))
                            (\v lam env -> f (unknownVariable rep v lam env))
                            (\t1 t2 lam env -> f (typesDontMatch rep t1 t2 lam env))
                            (\t lam env -> f (notAFunction rep t lam env))
                            (\lets lam env -> f (cyclicLet rep lets lam env))

instance Applicative (STReporter v t) where
    pure x = STReporter (\_ _ _ -> x) (\_ _ _ -> x) (\_ _ _ _ -> x) (\_ _ _ -> x) (\_ _ _ -> x)
    rf <*> rx = STReporter (\t lam env -> unknownType rf t lam env (unknownType rx t lam env))
                           (\v lam env -> unknownVariable rf v lam env (unknownVariable rx v lam env))
                           (\t1 t2 lam env -> typesDontMatch rf t1 t2 lam env
                                                  (typesDontMatch rx t1 t2 lam env))
                           (\t lam env -> notAFunction rf t lam env (notAFunction rx t lam env))
                           (\lets lam env -> cyclicLet rf lets lam env (cyclicLet rx lets lam env))

{-|
    A simple error reporter that doesn't provide much information.
-}
stockSTReporter :: (v -> String) -> (t -> String) -> STReporter v t String
stockSTReporter vshow tshow = STReporter {
      unknownType     = \t _ _        -> "The type: " ++ tshow t ++ " is not a known type"
    , unknownVariable = \v _ _        -> "The variable " ++ vshow v ++ " is not in scope"
    , typesDontMatch  = \fnd expt _ _ -> "Expected: " ++ tshow expt ++ ", found: " ++ tshow fnd
    , notAFunction    = \t _ _        -> "Tried to apply to: " ++ tshow t ++ " as if it were a function"
    , cyclicLet       = \lets _ _     ->
        "There is a cycle in the let dependencies: " ++ intercalate ", " (vshow . fst . fst <$> lets)
}

{-|
    Default reporter, applied show to variables and base types but also tries to prettyprint
    where it can.
-}
defaultSTReporter :: (SimpleType t, Show v, Show t) => STReporter v t String
defaultSTReporter = stockSTReporter show (prettyprintST show)

{-|
    Typecheck a simply-typed lambda calculus expression. Note that this doen't work well
    for typesystems that are more than just simply-typed.
-}
typecheckSTLC ::
       (SimpleType t, Ord v)
    => STReporter v t err    -- ^ The error reporter for type/name errors.
    -> TypingEnvironment v t -- ^ The current typing environment
    -> LambdaExpr v t        -- ^ the expression being typechecked
    -> Either [err] t        -- ^ The result, either a list of type/name errors or the type of the expression.
typecheckSTLC rep env expr = case expr of
    -- TODO: comment this better.
    -- TODO: redesign this, it's gotten messy.
    Var v ->
        case v `Map.lookup` vars env of
            -- The variable doesn't exist within the typing environment, return a unknownVariable error.
            Nothing -> Left [unknownVariable rep v expr env]
            -- The variable exists within the typing environment, return it's type.
            Just t -> Right t
    Let lets expr' ->
        case unlet lets expr' of
            Let lets' _ -> Left [cyclicLet rep lets' expr env]
            expr''              -> typecheckSTLC rep env expr''
    Apply fun arg ->
        let fun' = typecheckSTLC rep env fun
            arg' = typecheckSTLC rep env arg
        in case (fun', arg') of
            -- if both fun and arg typeerror independently, concatinate their errors
            (Left x, Left y) -> Left $ x ++ y
            _                -> do
                -- get the types of the function and argument expressions
                fun'type <- fun'
                arg'type <- arg'
                case reify fun'type of
                    Nothing -> Left [notAFunction rep fun'type expr env]
                    Just (t1, t2)
                        | arg'type == t1 -> Right t2
                        | otherwise -> Left [typesDontMatch rep arg'type t1 expr env] -- maybe be more specific?
    Lambda (v, t) expr' -> do
        -- if there are types in the bases of "t" that are not in the type universe then error.
        let unknownTypes = Set.toList $ Set.difference (bases t) (allTypes env)
        unless (null unknownTypes) $ Left ((\t' -> unknownType rep t' expr env) <$> unknownTypes)
        -- update what v refers to in the scope of expr'
        let env' = env { vars = Map.insert v t (vars env) }
        -- typecheck the expression with this new environment
        expr'type <- typecheckSTLC rep env' expr'
        -- return the type, which would be a function type of t to the expression's type.
        return (t /-> expr'type)

{-|
    given a function that prettyprints base types, pretty print the type with function arrows
    whenever a function type is present.
-}
prettyprintST :: SimpleType t => (t -> String) -> t -> String
prettyprintST f t =
    case reify t of
        Nothing -> f t
        Just (t1, t2) ->
            let t1'str = if isFunction t1 then "(" ++ prettyprintST f t1 ++ ")" else prettyprintST f t1
            in t1'str ++ " -> " ++ prettyprintST f t2

{-|
    Check if a simple type is a function type.
-}
isFunction :: SimpleType t => t -> Bool
isFunction = isJust . reify

{-|
    Check if a simple type is a base type.
-}
isBase :: SimpleType t => t -> Bool
isBase = not . isFunction

{-|
    Function retrives a set of all base types in the given lambda expression.
-}
basesOfExpr :: SimpleType t => LambdaExpr v t -> Set.Set t
basesOfExpr = bifoldr (\_ st -> st) (\t st -> bases t <> st) Set.empty

{-|
    Get a typing environment that assumes all the base types in an expression
    are valid.
-}
envFromExpr :: SimpleType t => LambdaExpr v t -> TypingEnvironment v t
envFromExpr = TypingEnvironment Map.empty . basesOfExpr
