{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
    , Substitution(..)
    -- ** Notation and related functions
    , quantifyMany
    , areAlphaEquivalent
    , (\-/)
    , generalise
    , generalise'
    , boundPolytypesOf
    , monotypesOf
    , isPolyType
    , toPolyType
    -- ** Typechecking context
    , SubsContext(..)
    , SubsContext'
    -- *** SubsContext lenses
    , subsMade
    , tape
) where

import           Calculi.Lambda.Cube.SimpleType
import           Data.Either.Combinators
import           Data.List.Ordered
import           Data.Maybe
import qualified Data.Map                       as Map
import qualified Data.Set                       as Set
import           Data.Semigroup
import           Control.Lens as Lens hiding ((&))

{-|
    A TypingContext
-}
data SubsContext t p = SubsContext {
      _subsMade :: Map.Map p t
    -- ^ The substitutions made so far, where the key is the poly type
    -- that is substituted and the value is what is substituting it.
    , _tape :: [p]
    -- ^ An infinite list of polytypes not present in the who typing context.
} deriving (Eq, Ord)
makeLenses ''SubsContext

{-|
    Datatype describing possible substitutions found by the `substitutions` Polymorphic
    typeclass method.
-}
data Substitution t p =
      Mutual p p
      -- ^ Two equivalent polytypes that could substitute eachother.
    | Replace t p
      -- ^ A substitution of type expression @t@ over polytype @p@
    deriving (Eq, Ord, Show)

{-|
    Note: only shows the first 10 elements of the infinte list.
-}
instance (Show t, Show p) => Show (SubsContext t p) where
    show (SubsContext s tp) = "SubsContext (" ++ show s ++ ") (" ++ show (take 10 tp) ++ ")"

{-|
    `SubsContext` but assumes the poly type representation of @t@ is the second argument.
-}
type SubsContext' t = SubsContext t (PolyType t)

{-|
    Class of typesystems that exhibit polymorphism.
-}
class (Ord (PolyType t), SimpleType t) => Polymorphic t where

    {-|
        The type that reports any possible errors that occur during unification.
    -}
    type UnifyError t :: *

    {-|
        Unify two given type expressions.

        ===Behavior

        *
          Law: A unification function between two terms must produce equivalent expressions
          when applied to the two terms

            @
            -- Two type expressions ...
            a, b :: t

            -- ... that are not equivalent ...
            a ==== b
            > False

            -- ... are equivalent when unified, or cannot be unified at all.
            case unify a b of
                Left err -> True -- This property doesn't care about failures
                Right u -> u a ==== u b
            > True
            @

        *
          Law: equivalent expressions always unify.

            @
            -- Two type expressions ...
            a, b :: t

            -- ... that are equivalent ...
            a ==== b
            > True

            -- ... will always unify.
            case unify a b of
                Left err -> False
                Right u -> u a ==== u b
            > True

            -- Additionally: "u a", "u b", "a", and "b" are all equivalent to eachother.
            @
    -}
    unify :: t -> t -> Either (UnifyError t) (t -> t)

    {-|
        The representation of a poly type, also reffered to as a type variable.
    -}
    type PolyType t :: *

    {-|
        Find the substitutions between two type expressions. If there's
        a mismatch in structure then report the values passed as a Left
        value.

        ===Behaviour

        * A substitution of a poly type \"a\" for mono type \"X\"

            >>> substitutions (X) (a)
            Right [Substitution (X) (a)]

        * Two type expressions have substitutions between eachother.

            >>> substitutions (a → B) (X → b)
            Right [Substitution (X) (a), Substitution (B) (b)]

        * A mutual substitution between two poly types.

            >>> substitutions (a) (b)
            Right [Mutual (a) (b)]

        * Mismatches in structure.

            >>> substitutions (X) (Y)
            Left [(X, Y)]

            >>> substitutions (C → x C) (x C)
            Left [(C → x C, x C)]

    -}
    substitutions :: t -> t -> Either [(t, t)] [Substitution t (PolyType t)]

    {-|
        Substitution application, given one type expression substituting a poly type and a
        target type expression, substitute all instances of the poly type in the target
        type expression with the type expression substituting it.

        ===Behaviour

        * Substituting all instance of \"a\" with \"X\"

            >>> applySubstitution X a (∀ a b. a → b → a)
            (∀ b. X → b → X)@

        * Substitution application in a type expression with a type constructor.

            >>> applySubstitution (X → Y) x (M x)
            (M (X → Y))

        * Applying a substitution to a type expression that doesn't contain the poly type
          being substituted

            >>> applySubstitution Y x (M Q)
            (M Q)
    -}
    applySubstitution :: t -> PolyType t -> t -> t

    {-|
        Quantify instances of a poly type in a type expression.

        ===Behaviour

        * Quantifying a poly type that appears in a type expression.

            >>> quantify a (a → X)
            (∀ a. a → X)

        * Quantifying a poly type that doesn't appear in a type expression

            >>> quantify a (b → X)
            (∀ a. b → X)
    -}
    quantify :: PolyType t -> t -> t

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Poly p".
    -}
    poly :: PolyType t -> t

    {-|
        Function that retrives all the poly types in a type, quantified
        or not.

        ===Behaviour

        * Type expression with some of it's poly types quantified.

            >>> polytypesOf (∀ a b. a → b → c d))
            Set.fromList [a, b, c, d]

        * Type expression with no quantified poly types.

            >>> polytypesOf (a → b → c)
            Set.fromList [a, b, c]

        * Type expression with no unquantified poly types.

            >>> polytypesOf (∀ c. X → c)
            Set.singleton (c)
    -}
    polytypesOf :: t -> Set.Set t

    {-|
        Function that retrives all the quantified poly types in
        a type expression.

        ===Behaviour

        * Type expression with some of it's poly types quantified.

            >>> quantifiedOf (∀ a b. a → b → c d))
            Set.fromList [a, b]

        * Type expression with no quantified poly types.

            >>> quantifiedOf (a → b → c)
            Set.empty

        * Type expression with no unquantified poly types.

            >>> quantifiedOf (∀ c. X → c)
            Set.singleton (c)
    -}
    quantifiedOf :: t -> Set.Set t

{-|
    Quantify a number of variables in a foldable data type.
-}
quantifyMany :: (Polymorphic t, Foldable f) => f (PolyType t) -> t -> t
quantifyMany ps t = foldr quantify t ps

{-|
    Infix `quantify`, looks a bit like @∀@ but doesn't interfere with unicode syntax extensions.
-}
(\-/) :: Polymorphic t => PolyType t -> t -> t
(\-/) = quantify

infixr 6 \-/

{-|
    All the unbound polytypes in a type expression.
-}
freePolytypesOf :: Polymorphic t => t -> Set.Set t
freePolytypesOf t = polytypesOf t `Set.difference` quantifiedOf t

{-|
    Bound polytypes of an expression.
-}
boundPolytypesOf :: Polymorphic t => t -> Set.Set t
boundPolytypesOf = quantifiedOf

{-|
    Monotypes of a type expression.
-}
monotypesOf :: Polymorphic t => t -> Set.Set t
monotypesOf t = Set.difference (bases t) (polytypesOf t)

{-|
    Quantify every free polytype in a type expression, excluding a
    set of polytypes to not quantify.

    >>> generalise Set.empty (x → y)
    (∀ x y. x → y)

    >>> generalise (Set.fromList [a, b]) (a → b → c)
    (∀ c. a → b → c)
-}
generalise :: forall t. Polymorphic t => Set.Set t -> t -> t
generalise exclude t = quantifyMany ftvsBare t where
    ftvsBare :: Set.Set (PolyType t)
    ftvsBare = Set.fromList $ snd <$> filter (flip Set.member ftvs . fst) polyTypes where
        ftvs = Set.difference (freePolytypesOf t) exclude
        polyTypes :: [(t, PolyType t)]
        polyTypes = fmap (\(Mutual a b) -> (poly a, b)) . fromRight [] $ substitutions t t

{-|
    `generalise` but with an empty exclusion set.
-}
generalise' :: Polymorphic t => t -> t
generalise' = generalise Set.empty

{-|
    Check if two types are equivalent, where equivalence is defined as the substitutions
    being made being symbolically identical, where binds and poly types appear in
    the same place but may have different names (this is Alpha Equivalence).

    >>> areAlphaEquivalent (∀ a. X → a) (∀ z. X → z)
    True

    >>> areAlphaEquivalent (M → X) (M → X)
    True

    >>> areAlphaEquivalent (∀ a. a) (∀ z. z → z)
    False

    >>> areAlphaEquivalent (∀ a. a -> a) (∀ b. c -> b)
    False
-}
areAlphaEquivalent :: forall t. Polymorphic t => t -> t -> Bool
areAlphaEquivalent x y =
    let -- "go" is a terrible thing to name this, it's completely non-descriptive.
        go :: Substitution t (PolyType t)
           -> Maybe (Map.Map (PolyType t) (PolyType t))
           -> Maybe (Map.Map (PolyType t) (PolyType t))
        go _ Nothing               = Nothing -- If there's no Map, then return nothing
        go (Replace _ _ ) _   = Nothing -- If a non-mutual substitution appears, the type expressions aren't alpha equivalent
        go (Mutual p1 p2) (Just m) = do
            lookP1 <- return . fromMaybe True $ do
                lookP1' <- Map.lookup p1 m
                return (lookP1' == p2)
            lookP2 <- return . fromMaybe True $ do
                lookP1' <- Map.lookup p2 m
                return (lookP1' == p1)
            if lookP1 && lookP2 then return (Map.fromList [(p1, p2), (p2, p1)] <> m) else Nothing
    in isJust . fromRight Nothing $ foldr go (Just Map.empty) . nubSort <$> substitutions x y

{-|
    Tests if a type expression is a base poly type.

    >>> isPolyType (∀ a. a)
    False

    >>> isPolyType (a)
    True

    >>> isPolyType (b → c)
    False
-}
isPolyType :: Polymorphic t => t -> Bool
isPolyType t =
    fromRight False $ substitutions t t <&> \case
        [Mutual a b] -> a == b && t ==== poly a
        _            -> False

{-|
    Pull out a poly type representation from a poly type.
-}
toPolyType :: Polymorphic t => t -> Maybe (PolyType t)
toPolyType t = case substitutions t t of
    Right [Mutual a _]
        | poly a == t  -> Just a
    _                  -> Nothing
