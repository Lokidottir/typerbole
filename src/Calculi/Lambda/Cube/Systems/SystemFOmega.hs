{-# LANGUAGE LambdaCase #-}
module Calculi.Lambda.Cube.Systems.SystemFOmega where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Inferable
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Semigroup
import qualified Data.Set                        as Set
import qualified Data.Map                        as Map
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
    | Bind p (SystemFOmega m p)
      -- ^ A binding of a poly type variable in an expression, i.e. the "@∀ a.@" in "@∀ a. a@"
    | TypeAp (SystemFOmega m p) (SystemFOmega m p)
      -- ^ Type application.
    deriving (Eq, Ord, Show, Read)

instance Bifunctor SystemFOmega where
    bimap f g =
        let bimap' = bimap f g
        in \case
            Mono m         -> Mono (f m)
            FunctionArrow  -> FunctionArrow
            Poly p         -> Poly (g p)
            Bind p sf      -> Bind (g p) (bimap' sf)
            TypeAp sf1 sf2 -> TypeAp (bimap' sf1) (bimap' sf2)

instance Bifoldable SystemFOmega where
    bifoldr f g z _sf =
        let bifoldr'' = bifoldr f g
        in case _sf of
            Mono m         -> f m z
            FunctionArrow  -> z
            Poly p         -> g p z
            Bind p sf      -> g p (bifoldr'' z sf)
            TypeAp sf1 sf2 -> bifoldr'' (bifoldr'' z sf2) sf1

instance (Ord m, Ord p) => SimpleType (SystemFOmega m p) where
    abstract a = TypeAp (TypeAp FunctionArrow a)

    reify (TypeAp (TypeAp FunctionArrow a) b) = Just (a, b)
    reify (Bind _ sf)                         = reify sf
    reify _                                   = Nothing

    bases = \case
        Bind p sf    -> Set.insert (Poly p) (bases sf)
        TypeAp tl tr -> bases tl `Set.union` bases tr
        a            -> Set.singleton a


instance (Ord m, Ord p) => Polymorphic (SystemFOmega m p) where
    substitutions _x _y = case (_x, _y) of
        -- need to skip quantifiers on the left hand side
        (Bind _ sf, y) -> substitutions sf y
        -- Only poly types can actually be substituted, so if a poly type is
        -- on the right hand side then the left hand side is it's substitution
        (x, y@Poly{})  -> Just [(x, y)]
        -- Binds require recursing on it's type expr
        (x, Bind _ sf) -> substitutions x sf
        (TypeAp tl1 tr1, TypeAp tl2 tr2)
                       -> substitutions tl1 tl2 <> substitutions tr1 tr2
        _              -> Nothing

    applySubstitution sub target = applySubstitution' where
        canSub = sub `canSubstitute` target
        -- Might have a case of premature best-practices
        applySubstitution' = \case
            m@Mono{} -> m
            FunctionArrow -> FunctionArrow
            p@Poly{}
                | canSub && p == target -> sub
                | otherwise             -> p
            Bind p sf
                | Poly p == target -> applySubstitution' sf
                | otherwise        -> Bind p (applySubstitution' sf)
            TypeAp tl tr -> TypeAp (applySubstitution' tl) (applySubstitution' tr)

instance (Ord m, Ord p) => HigherOrder (SystemFOmega m p) where
    kind = \case
        m@Mono{}      -> Var m
        -- The function arrow (→ in the psudocode) is a mono type of the kind (* -> * -> *)
        FunctionArrow -> Var FunctionArrow
        p@Poly{}      -> Var p
        Bind p sf     -> Lambda (Poly p, star) (kind sf)
        TypeAp tl tr  -> Apply (kind tl) (kind tr)

    unkind = \case
        Var x                 -> x
        Apply x y             -> TypeAp (unkind x) (unkind y)
        Lambda (Poly p, _) sf -> Bind p (unkind sf)
        Lambda _ _            -> error "(SystemFOmega) non-poly variable bound by lambda during unkinding"
        lt@Let{}              ->
            case deepUnlet lt of
                Let{} -> error "(SystemFOmega) cyclic let expression during unkinding"
                sf    -> unkind sf


instance (Ord m, Ord p, Enum p) => HMInferable (SystemFOmega m p) where
    ftvs = \case
        poly@(Poly _) -> Set.singleton poly
        Bind p sf     -> Set.delete (Poly p) (ftvs sf)
        TypeAp tl tr  -> ftvs tl `Set.union` ftvs tr
        _             -> Set.empty

    nptTape env = Poly <$> [succ maxP ..] where
        -- Find the largest poly element in the type expression
        maxP = maximum (bifoldr (flip const) max (toEnum 0) <$> vars env)

instance (Ord m, Ord p, Arbitrary m, Arbitrary p) => Arbitrary (SystemFOmega m p) where
    arbitrary = do
        let arbApTy = TypeAp <$> arbitrary <*> arbitrary
        let arbBind = Bind <$> arbitrary <*> arbitrary
        let arbFun  = abstract <$> arbitrary <*> arbitrary
        let arbBase = [Poly <$> arbitrary, Mono <$> arbitrary]
        oneof ([arbApTy, arbBind, arbFun] ++ arbBase)

    shrink (TypeAp x y) = [x, y]
    shrink (Bind _ sf) = [sf]
    shrink _ = []

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
    Bind p st -> Bind p (markAsFunctionArrow sub st)
    TypeAp t1 t2 -> TypeAp (markAsFunctionArrow sub t1) (markAsFunctionArrow sub t2)
