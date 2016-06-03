{-# LANGUAGE LambdaCase #-}
module Calculi.Lambda.Cube.Systems.SystemFOmega where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Inferable
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import qualified Language.Haskell.TH.Lift as TH
import           Data.Bifoldable
import           Data.Bifunctor.TH
import           Data.Generics
import           Data.Random.Generics
import           Data.Semigroup
import qualified Data.Set                        as Set
import           Test.QuickCheck

{-|
    A data type representing the components of System-Fω.
-}
data SystemFOmega m p =
      Mono m
      -- ^ A mono type
    | FunctionArrow
      -- ^ Explicitly stated mono type of kind @(* → * → *)@ for type application reasons
    | Poly p
      -- ^ A poly type, i.e. the "@a@" in "@∀ a. a → a@"
    | Forall p (SystemFOmega m p)
      -- ^ A binding of a poly type variable in an expression, i.e. the "@∀ a.@" in "@∀ a. a@"
    | TypeAp (SystemFOmega m p) (SystemFOmega m p)
      -- ^ Type application.
    deriving (Eq, Ord, Show, Read, Data)

deriveBifunctor ''SystemFOmega
deriveBifoldable ''SystemFOmega
deriveBitraversable ''SystemFOmega
TH.deriveLift ''SystemFOmega

instance (Ord m, Ord p) => SimpleType (SystemFOmega m p) where
    type MonoType (SystemFOmega m p) = m

    abstract a = TypeAp (TypeAp FunctionArrow a)

    reify (TypeAp (TypeAp FunctionArrow a) b) = Just (a, b)
    reify _                                   = Nothing

    bases = \case
        Forall p sf  -> Set.insert (Poly p) (bases sf)
        TypeAp tl tr -> bases tl `Set.union` bases tr
        a            -> Set.singleton a

    mono = Mono


instance (Ord m, Ord p) => Polymorphic (SystemFOmega m p) where

    type PolyType (SystemFOmega m p) = p

    substitutions = curry $ \case
        -- need to skip quantifiers on the left hand side
        (Forall _ expr, target) -> substitutions expr target
        -- Only poly types can actually be substituted, so if a poly type is
        -- on the right hand side then the left hand side is it's substitution
        (expr, Poly p)          -> Just [(expr, p)]
        -- Foralls require recursing on it's type expr
        (expr, Forall _ target) -> substitutions expr target
        (TypeAp tl1 tr1, TypeAp tl2 tr2)
                                -> (<>) <$> substitutions tl1 tl2 <*> substitutions tr1 tr2
        (expr, target)
            | expr == target -> Just []
            | otherwise -> Nothing

    applySubstitution sub target = applySubstitution' where
        applySubstitution' = \case
            m@Mono{}          -> m
            FunctionArrow     -> FunctionArrow
            p'@(Poly p)
                | p == target -> sub
                | otherwise   -> p'
            Forall p sf
                | p == target -> applySubstitution' sf
                | otherwise   -> Forall p (applySubstitution' sf)
            TypeAp tl tr      -> TypeAp (applySubstitution' tl) (applySubstitution' tr)

    quantify = Forall
    unquantify (Forall a b) = Just (a, b)
    unquantify _ = Nothing

    poly = Poly

    ftvs = \case
        p@(Poly _)    -> Set.singleton p
        Forall p sf   -> Set.delete (Poly p) (ftvs sf)
        TypeAp tl tr  -> ftvs tl <> ftvs tr
        _             -> Set.empty

instance (Ord m, Ord p) => HigherOrder (SystemFOmega m p) where

    type Kind (SystemFOmega m p) = Star

    kind = \case
        m@Mono{}      -> Var m
        -- The function arrow (→ in the psudocode) is a mono type of the kind (* -> * -> *)
        FunctionArrow -> Var FunctionArrow
        p@Poly{}      -> Var p
        Forall p sf   -> Lambda (Poly p, star) (kind sf)
        TypeAp tl tr  -> Apply (kind tl) (kind tr)

    unkind = \case
        Var x                 -> Just x
        Apply x y             -> TypeAp <$> unkind x <*> unkind y
        Lambda (Poly p, _) sf -> Forall p <$> unkind sf
        lt@Let{}              ->
            case deepUnlet lt of
                Let{} -> Nothing
                sf    -> unkind sf
        _                     -> Nothing

    typeap = TypeAp
    untypeap (TypeAp a b) = Just (a, b)
    untypeap _ = Nothing

instance (Data m, Data p, Arbitrary m, Arbitrary p) => Arbitrary (SystemFOmega m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized generatorP

{-|
    Given a function arrow representation of type @m@, replace all
    matching mono types with the function arrow.
-}
markAsFunctionArrow :: Eq m =>  m -> SystemFOmega m p -> SystemFOmega m p
markAsFunctionArrow sub = \case
    m@(Mono x)
        | x == sub -> FunctionArrow
        | otherwise -> m
    FunctionArrow -> FunctionArrow
    Poly x -> Poly x
    Forall p st -> Forall p (markAsFunctionArrow sub st)
    TypeAp t1 t2 -> TypeAp (markAsFunctionArrow sub t1) (markAsFunctionArrow sub t2)
