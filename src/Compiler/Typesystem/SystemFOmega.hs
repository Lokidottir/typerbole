{-# LANGUAGE LambdaCase #-}
module Compiler.Typesystem.SystemFOmega where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import           Compiler.Typesystem.SimplyTyped (SimplyTyped)
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

    substitutions =
        let (<><>) :: (Semigroup s1, Semigroup s2) => Either s1 s2 -> Either s1 s2 -> Either s1 s2
            (<><>) = curry $ \case
                (Left a, Left b) -> Left (a <> b)
                (a, b) -> (<>) <$> a <*> b
        in curry $ \case
            (Forall _ expr1    , expr2)              -> substitutions expr1 expr2
            (expr1             , Forall _ expr2)     -> substitutions expr1 expr2
            (Poly p1           , Poly p2)            -> Right [Mutual p1 p2]
            (expr              , Poly p)             -> Right [Substitution expr p]
            (Poly p            , expr)               -> Right [Substitution expr p]
            (TypeAp arg1 ret1  , TypeAp arg2 ret2) -> substitutions arg1 arg2 <><> substitutions ret1 ret2
            (expr1             , expr2)
                | expr1 == expr2 -> Right []
                | otherwise      -> Left [(expr1, expr2)]

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

    freeTypeVariables = \case
        p@(Poly _)    -> Set.singleton p
        Forall p sf   -> Set.delete (Poly p) (freeTypeVariables sf)
        TypeAp tl tr  -> freeTypeVariables tl <> freeTypeVariables tr
        _             -> Set.empty

instance (Ord m, Ord p) => HigherOrder (SystemFOmega m p) where

    type Kindsystem (SystemFOmega m p) = (SimplyTyped Star)

    kind = \case
        m@Mono{}      -> Constant m
        -- The function arrow (→ in the psudocode) is a mono type of the kind (* -> * -> *)
        FunctionArrow -> Constant FunctionArrow
        p@Poly{}      -> Constant p
        Forall p sf   -> kind sf
        TypeAp tl tr  -> Apply (kind tl) (kind tr)

    typeap = TypeAp
    untypeap (TypeAp a b) = Just (a, b)
    untypeap _ = Nothing

instance (Data m, Data p, Arbitrary m, Arbitrary p) => Arbitrary (SystemFOmega m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized (generatorSRWith aliases) where
        aliases :: [AliasR Gen]
        aliases = [
                    aliasR (\() -> arbitrary :: Gen m)
                  , aliasR (\() -> arbitrary :: Gen p)
                  ]

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
