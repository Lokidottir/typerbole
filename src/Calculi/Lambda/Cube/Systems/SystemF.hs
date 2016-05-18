module Calculi.Lambda.Cube.Systems.SystemF where

import Data.Bifunctor.TH
import Calculi.Lambda.Cube.SimpleType
import Calculi.Lambda.Cube.Polymorphic
import qualified Data.Set as Set
import Data.Generics
import Data.Monoid

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
    abstract = Function

    reify (Function a b) = Just (a, b)
    reify _              = Nothing

    bases = \case
        Function fun arg -> bases fun <> bases arg
        Forall p expr    -> Set.insert (Poly p) (bases expr)
        expr             -> Set.singleton expr

instance (Ord m, Ord p) => Polymorphic (SystemF m p) where
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
            m@Mono{}                         -> m
            p@Poly{}
                | canSub && p == target      -> sub
                | otherwise                  -> p
            Forall p expr
                | canSub && Poly p == target -> applySubstitution' expr
                | otherwise                  -> Forall p (applySubstitution' expr)
            Function fune arge               -> Function (applySubstitution' fune) (applySubstitution' arge)
