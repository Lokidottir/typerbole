module Calculi.Lambda.Cube.Systems.SystemF where

import           Data.Bifunctor.TH
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Polymorphic
import qualified Data.Set as Set
import           Data.Random.Generics
import           Data.Generics
import           Data.Monoid
import           Test.QuickCheck

{-|
    An implementation of System-F, similar to haskell's own typesystems but without
    type-level functions beyond (→)
-}
data SystemF m p =
      Mono m
    | Poly p
    | Function (SystemF m p) (SystemF m p)
    | Forall p (SystemF m p)
    deriving (Eq, Ord, Show, Read, Data)

deriveBifunctor ''SystemF
deriveBifoldable ''SystemF
deriveBitraversable ''SystemF

instance (Ord m, Ord p) => SimpleType (SystemF m p) where

    type MonoType (SystemF m p) = m

    abstract = Function

    reify (Function a b) = Just (a, b)
    reify _              = Nothing

    bases = \case
        Function fun arg -> bases fun <> bases arg
        Forall p expr    -> Set.insert (Poly p) (bases expr)
        expr             -> Set.singleton expr

    mono = Mono

instance (Ord m, Ord p) => Polymorphic (SystemF m p) where

    type PolyType (SystemF m p) = p

    substitutions = curry $ \case
        (Forall _ expr, target) -> substitutions expr target
        (expr, target@Poly{})   -> Just [(expr, target)]
        (expr, Forall _ target) -> substitutions expr target
        (Function fune arge, Function funt argt)
                                -> (<>) <$> substitutions fune funt <*> substitutions arge argt
        (expr, target)
            | expr == target -> Just []
            | otherwise      -> Nothing

    applySubstitution sub target = applySubstitution' where
        canSub = sub `canSubstitute` target

        applySubstitution' = \case
            m@Mono{}                     -> m
            p@Poly{}
                | canSub && p == target  -> sub
                | otherwise              -> p
            Forall p expr
                | canSub && Poly p == target -> applySubstitution' expr
                | otherwise              -> Forall p (applySubstitution' expr)
            Function fune arge           -> Function (applySubstitution' fune) (applySubstitution' arge)

    quantify = Forall
    unquantify (Forall a b) = Just (a, b)
    unquantify _ = Nothing

    poly = Poly

instance (Arbitrary m, Data m, Arbitrary p, Data p) => Arbitrary (SystemF m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized generatorP
