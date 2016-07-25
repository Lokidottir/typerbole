{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
    , Substitution(..)
    -- ** Notation and related functions
    , areAlphaEquivalent
    , (≣)
    , (\-/)
    , generalise
    , generalise'
    , polytypesOf
    , boundPolytypesOf
    , monotypesOf
    , isPolyType
    -- ** Typechecking context
    , SubsContext(..)
    , SubsContext'
    -- *** SubsContext lenses
    , subsMade
    , tape
) where

import           Calculi.Lambda.Cube.SimpleType
import           Data.Either.Combinators
import qualified Data.Map                       as Map
import qualified Data.Set                       as Set
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
    | Substitution t p
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
    Infix `areAlphaEquivalent`
-}
(≣) :: Polymorphic t => t -> t -> Bool
(≣) = areAlphaEquivalent

infix 4 ≣

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
generalise exclude t = foldr quantify t ftvsBare where
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
-}
areAlphaEquivalent :: forall t. Polymorphic t => t -> t -> Bool
areAlphaEquivalent x y = fromRight False $ all isMutual <$> subs where
    subs = substitutions x y

    isMutual (Mutual _ _) = True
    isMutual _            = False

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
        [Mutual a b] -> a == b && t == poly a
        _            -> False
