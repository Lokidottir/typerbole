{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
    , Substitution(..)
    -- ** Notation and related functions
    , areEquivalent
    , (≣)
    , (\-/)
    , generalise
    , generalise'
    , typeVariables
    , boundTypeVariables
    , typeConstants
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
    -- ^ The substitutions made so far, where the key is the type variable
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

        * Quantifying a type variable that appears in a type expression.

            >>> quantify a (a → X)
            (∀ a. a → X)

        * Quantifying a type variable that doesn't appear in a type expression

            >>> quantify a (b → X)
            (∀ a. b → X)
    -}
    quantify :: PolyType t -> t -> t

    {-|
        Split a quantification into it's variable being quantified and
        the expression targeted by the quantification. A safe inverse of `quantify`.

        ===Behaviour

        * Unquantifying a type expression that quantifies a single poly type.

            >>> unquantify (∀ a. a → b)
            Just (a, a → b)

        * Unquantifying a type expression that quantifies multiple poly types

            >>> unquantify (∀ a b. a b)
            Just (a, ∀ b. a b)

        * Unquantifying a type expression that quantifies none of it's poly types.

            >>> unquantify (A b)
            Nothing
    -}
    unquantify :: t -> Maybe (PolyType t, t)

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Poly p".
    -}
    poly :: PolyType t -> t

    {-|
        Function retrives all the free type variables in a type.
        If the type is itself an unbound poly type, then that is returned.

        ===Behaviour

        * Type expression with some of it's poly types quantified.

            >>> freeTypeVariables (∀ a b. a → b → c d))
            Set.fromList [c, d]

        * Type expression with no quantified poly types.

            >>> freeTypeVariables (a → b → c)
            Set.fromList [a, b, c]

        * Type expression with no unquantified poly types.

            >>> freeTypeVariables (∀ c. X → c)
            Set.empty
    -}
    freeTypeVariables :: t -> Set.Set t

{-|
    Infix `areEquivalent`
-}
(≣) :: Polymorphic t => t -> t -> Bool
(≣) = areEquivalent

infix 4 ≣

{-|
    Infix `quantify`, looks a bit like @∀@ but doesn't interfere with unicode syntax extensions.
-}
(\-/) :: Polymorphic t => PolyType t -> t -> t
(\-/) = quantify

infixr 6 \-/

{-|
    All the type variables in a type expression, bound or unbound.
-}
typeVariables :: Polymorphic t => t -> Set.Set t
typeVariables t = Set.fromList . concatMap (\(Mutual a b) -> poly <$> [a, b]) $ fromRight [] (substitutions t t)

{-|
    Bound type variables of an expression.
-}
boundTypeVariables :: Polymorphic t => t -> Set.Set t
boundTypeVariables t = Set.difference (typeVariables t) (freeTypeVariables t)

{-|
    Type constants/Mono types of a type expression.
-}
typeConstants :: Polymorphic t => t -> Set.Set t
typeConstants t = Set.difference (bases t) (typeVariables t)

{-|
    Quantify every free type variable in a type expression, excluding a
    set of free type variables to not quantify.

    >>> generalise Set.empty (x → y)
    (∀ x y. x → y)

    >>> generalise (Set.fromList [a, b]) (a → b → c)
    (∀ c. a → b → c)
-}
generalise :: forall t. Polymorphic t => Set.Set t -> t -> t
generalise exclude t = foldr quantify t ftvsBare where
    ftvsBare :: Set.Set (PolyType t)
    ftvsBare = Set.fromList $ snd <$> filter (flip Set.member ftvs . fst) polyTypes where
        ftvs = Set.difference (freeTypeVariables t) exclude
        polyTypes :: [(t, PolyType t)]
        polyTypes = fmap (\(Mutual a b) -> (poly a, b)) . fromRight [] $ substitutions t t

{-|
    `generalise` but with an empty exclusion set.
-}
generalise' :: Polymorphic t => t -> t
generalise' = generalise Set.empty

{-|
    Check if two types are equivalent, where equivalence is defined as the substitutions
    being made being symbolically identical, where binds and type variables appear in
    the same place but may have different names (this is Alpha Equivalence).

    >>> areEquivalent (∀ a. X → a) (∀ z. X → z)
    True

    >>> areEquivalent (M → X) (M → X)
    True

    >>> areEquivalent (∀ a. a) (∀ z. z → z)
    False
-}
areEquivalent :: forall t. Polymorphic t => t -> t -> Bool
areEquivalent x y = fromRight False $ all isMutual <$> subs where
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
