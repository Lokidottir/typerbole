{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
import           Calculi.Lambda
import           Calculi.Lambda.Cube
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.Polymorphic.Unification
import           Calculi.Lambda.Cube.Systems.SimplyTyped  as ST
import           Calculi.Lambda.Cube.Systems.SystemF      as SF
import           Calculi.Lambda.Cube.Systems.SystemFOmega as SFO
import           Data.Maybe
import           Data.Generics
import           Data.Semigroup
import           Control.Arrow hiding (first, second)
import           Data.Either.Combinators
import           Data.Bifunctor
import           Debug.Trace
import qualified Data.Set as Set
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

main :: IO ()
main = hspec $
        describe "Type systems follow laws and properties" $ do
            describe "SimplyTyped" $
                followsSimpleType (arbitrary :: Gen SimplyTyped')
            describe "System-F" $ do
                followsSimpleType (arbitrary :: Gen SystemF')
                followsPolymorphic (arbitrary :: Gen SystemF')
            describe "System-Fω" $ do
                followsSimpleType (arbitrary :: Gen SystemFOmega')
                followsPolymorphic (arbitrary :: Gen SystemFOmega')
                followsHigherOrder (arbitrary :: Gen SystemFOmega')

type SimplyTyped' = SimplyTyped AlphabetUpper
type SystemFOmega' = SystemFOmega AlphabetUpper AlphabetLow
type SystemF' = SF.SystemF AlphabetUpper AlphabetLow

followsSimpleType :: forall t. (SimpleType t, Show t, Arbitrary t) => Gen t -> Spec
followsSimpleType gen = describe "SimpleType laws and properties" $
    prop "follows abstract-reify inverse law" $ (abstractInverse :: t -> t -> Bool)

followsPolymorphic :: forall t.
                      (
                        Polymorphic t
                      , Show t
                      , Arbitrary t
                      , Arbitrary (PolyType t)
                      , Show (PolyType t)
                      , Enum (PolyType t)
                      )
                   => Gen t -> Spec
followsPolymorphic gen = describe "Polymorphic laws and properties" $ do
    prop "equivalence is reflexive"
        ((\ !ty -> ty ≣ ty) :: t -> Bool)
    prop "follows quantify-unquantify inverse law"
        (quantifyInverse :: (PolyType t) -> t -> Bool)
    prop "follows type-ordering rule 1"
        (typeOrderingRule :: t -> Bool)
    modifyMaxSuccess (const 1000) . prop "follows unification rule: when U(t, t') = V; V(t) ≣ V(t')" $
        forAll(arbitrary `suchThat` unifyR1Predicate)
            (uncurry unifyR1 :: ((t, t) -> Bool))

followsHigherOrder :: forall t. (Show t, HigherOrder t, Arbitrary t) => Gen t -> Spec
followsHigherOrder gen = describe "HigherOrder laws and properties" $ do
    prop "follows kind-unkind inverse law" $
        ((\ !ty -> unkind (kind ty) == Just ty) :: t -> Bool)
    prop "follows typeap-untypeap inverse law" $ (typeapInverse ::  t -> t -> Bool)

{-|
    Check that `reify` is the inverse (within a Maybe) of `abstract`.
-}
abstractInverse :: (SimpleType t) => t -> t -> Bool
abstractInverse !ta !tb = fmap (uncurry (/->)) (reify (ta /-> tb)) == Just (ta /-> tb)

quantifyInverse :: (Polymorphic t) => PolyType t -> t -> Bool
quantifyInverse !ta !tb =
    fmap (uncurry quantify) (unquantify (quantify ta tb)) == Just (quantify ta tb)

typeapInverse :: HigherOrder t => t -> t -> Bool
typeapInverse !ta !tb = fmap (uncurry (/$)) (untypeap (ta /$ tb)) == Just (ta /$ tb)

typeOrderingRule :: (Enum e, Polymorphic t, PolyType t ~ e) => t -> Bool
typeOrderingRule !t =
    fromRight False . runUnify' (UnifyState $ enumFrom (toEnum 10000)) $ (poly (toEnum 9999) ⊑ t)

unifyR1 :: forall t e. (Enum e, Polymorphic t, Show t, PolyType t ~ e) => t -> t -> Bool
unifyR1 !t1 !t2 =
    -- If the unification returns errors, then return true as
    -- this rule is checking the property itself, not the substitution errors.
    fromRight True . runUnify' (UnifyState $ enumFrom (toEnum 9000)) $ do
        subs <- unify t1 t2
        u <- eitherToError (applyAllSubsGr subs)
        return (u t1 ≣ u t2)

{-
    The input predicate for unifyR1; the type variables in each expression
    must be disjoint and there must be valid substitutions between the two expressions.
-}
unifyR1Predicate (t1, t2) =
    t1'tvs `disjoint` t2'tvs && hasSubstitutions' where
        hasSubstitutions' = fromRight False . runUnify' ustate $ hasSubstitutions t1 t2

        ustate = UnifyState (filter (flip Set.notMember alltvs . poly) (toEnum <$> [0..]))

        alltvs = t1'tvs <> t2'tvs

        t1'tvs = typeVariables t1
        t2'tvs = typeVariables t2

disjoint a b = Set.difference a b == a

newtype AlphabetLow = AlphabetLow Integer deriving (Eq, Ord, Enum, Data, Typeable)

instance Arbitrary AlphabetLow where
    arbitrary = AlphabetLow <$> elements [0..35]

instance Show AlphabetLow where
    show (AlphabetLow n) = char : if suffix == 0 then
        "" else show suffix where
            suffix = (n - charNum) `div` 36

            charNum = n `mod` 36

            char = (cycle ['a'..'z']) !! fromEnum charNum

newtype AlphabetUpper = AlphabetUpper Integer deriving (Eq, Ord, Enum, Data, Typeable)

instance Arbitrary AlphabetUpper where
    arbitrary = AlphabetUpper <$> elements [0..35]

instance Show AlphabetUpper where
    show (AlphabetUpper n) = char : if suffix == 0 then "" else (show suffix) where
        suffix = (n - charNum) `div` 36

        charNum = n `mod` 36

        char = (cycle ['A'..'Z']) !! fromEnum charNum
