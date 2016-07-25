{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-|
    <https://en.wikipedia.org/wiki/System_F#System_F.CF.89 System Fω> is a System F that allows
    type operators (@Set Int@, @List Int@, @Either Int Bool@ etc.)
-}
module Compiler.Typesystem.SystemFOmega (
      SystemFOmega
    , markAsFunctionArrow
) where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.HigherOrder
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Typechecking
import           Compiler.Typesystem.SimplyTyped (SimplyTyped)
import qualified Language.Haskell.TH.Lift as TH
import           Data.Bifunctor.TH
import           Data.Generics
import           Data.Random.Generics
import           Data.Semigroup
import qualified Data.Set                        as Set
import           Test.QuickCheck

{-|
    A data type representing the components of System-Fω, with a parameterized
    higher-order typesystem @k@.
-}
data SystemFOmega m p k =
      Mono m
      -- ^ A mono type
    | FunctionArrow
      -- ^ Explicitly stated mono type of kind @(* → * → *)@ for type application reasons
    | Poly p
      -- ^ A poly type, i.e. the "@a@" in "@∀ a. a → a@"
    | Forall (p, k) (SystemFOmega m p k)
      -- ^ A binding of a poly type in a type expression, i.e. the "@∀ a.@" in "@∀ a. a@"
    | TypeAp (SystemFOmega m p k) (SystemFOmega m p k)
      -- ^ Type application.
    deriving (Eq, Ord, Show, Read, Data)

infixl 0 `TypeAp`

deriveBifunctor ''SystemFOmega
deriveBifoldable ''SystemFOmega
deriveBitraversable ''SystemFOmega
TH.deriveLift ''SystemFOmega

instance (Ord m, Ord p, Ord k) => SimpleType (SystemFOmega m p (Maybe k)) where
    -- SystemFOmega's mono type is it's type parameter 'm'
    type MonoType (SystemFOmega m p (Maybe k)) = m

    -- Making a function type from one type to another involves
    -- using type application on the function arrow.
    abstract a b = FunctionArrow `TypeAp` a `TypeAp` b

    reify (FunctionArrow `TypeAp` a `TypeAp` b) = Just (a, b)
    reify _                                     = Nothing

    bases = \case
        Forall _ sf  -> bases sf
        TypeAp tl tr -> bases tl `Set.union` bases tr
        a            -> Set.singleton a

    mono = Mono

    equivalent = areAlphaEquivalent

instance (Ord m, Ord p, Ord k) => Polymorphic (SystemFOmega m p (Maybe k)) where

    type PolyType (SystemFOmega m p (Maybe k)) = p

    substitutions = curry $ \case
            (Forall _ expr1    , expr2)              -> substitutions expr1 expr2
            (expr1             , Forall _ expr2)     -> substitutions expr1 expr2
            (Poly p1           , Poly p2)            -> Right [Mutual p1 p2]
            (expr              , Poly p)             -> Right [Substitution expr p]
            (Poly p            , expr)               -> Right [Substitution expr p]
            (TypeAp arg1 ret1  , TypeAp arg2 ret2)   -> substitutions arg1 arg2 <><> substitutions ret1 ret2
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
            Forall declr@(p, _) sf
                | p == target -> applySubstitution' sf
                | otherwise   -> Forall declr (applySubstitution' sf)
            TypeAp tl tr      -> TypeAp (applySubstitution' tl) (applySubstitution' tr)

    quantify = Forall . flip (,) Nothing

    poly = Poly

    quantifiedOf = \case
        Forall (p, _) texpr -> Set.insert (poly p) $ quantifiedOf texpr
        TypeAp texpr1 texpr2 -> quantifiedOf texpr1 <> quantifiedOf texpr2
        _ -> Set.empty

instance (
           Ord m
         , Ord p
         , Ord k
         , Inferable (SystemFOmega m p) k
         , TypingContext (SystemFOmega m p) k ~ InferenceContext (SystemFOmega m p) k)
         => HigherOrder (SystemFOmega m p (Maybe k)) where
    type Kindsystem (SystemFOmega m p (Maybe k)) = k

    type KindError (SystemFOmega m p (Maybe k)) =
        Either (InferError (SystemFOmega m p) k)
               (TypeError (SystemFOmega m p) k)

    type KindContext (SystemFOmega m p (Maybe k)) = (TypingContext (SystemFOmega m p) k)

    kindcheck env texpr = case infer env texpr of
        Left errs -> Left (Left <$> errs)
        Right (env', texpr') -> case typecheck env' texpr' of
            Left errs -> Left (Right <$> errs)
            Right (env'', texpr'') -> Right (env'', texpr'')

    typeap = TypeAp

    untypeap (TypeAp a b) = Just (a, b)
    untypeap _ = Nothing

instance (Data m, Data p, Data k, Arbitrary m, Arbitrary p, Arbitrary k) => Arbitrary (SystemFOmega m p k) where
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
markAsFunctionArrow :: Eq m => m -> SystemFOmega m p k -> SystemFOmega m p k
markAsFunctionArrow sub = \case
    m@(Mono x)
        | x == sub -> FunctionArrow
        | otherwise -> m
    FunctionArrow -> FunctionArrow
    p@Poly{} -> p
    Forall p st -> Forall p (markAsFunctionArrow sub st)
    TypeAp t1 t2 -> TypeAp (markAsFunctionArrow sub t1) (markAsFunctionArrow sub t2)
