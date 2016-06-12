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
    , SimpleTypingContext(..)
    , vars
    , allTypes
    -- * Other functions
    , prettyprintST
    , isFunction
    , isBase
    , basesOfExpr
    , envFromExpr
) where

import           Calculi.Lambda
import           Control.Monad
import           Control.Lens
import           Data.Bifoldable
import           Data.List
import qualified Data.Map        as Map
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set        as Set
import           Test.QuickCheck

data SimpleTypingContext v t = SimpleTypingContext {
      _vars     :: Map.Map v t
    , _allTypes :: Set.Set t
} deriving (Show, Read, Eq, Ord)

makeLenses ''SimpleTypingContext

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
envFromExpr :: SimpleType t => LambdaExpr v t -> SimpleTypingContext v t
envFromExpr = SimpleTypingContext Map.empty . basesOfExpr
