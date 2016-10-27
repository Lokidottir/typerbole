{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
import           Calculi.Lambda
import           Calculi.Lambda.Cube
import           Calculi.Lambda.Cube.Polymorphic
import           Compiler.Typesystem.SimplyTyped  as ST
import           Compiler.Typesystem.SystemF      as SF
import           Compiler.Typesystem.SystemFOmega as SFO
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
main = hspec $ do
    describe "Type systems follow laws and properties" $ do
        describe "SimplyTyped" $
            followsSimpleType (arbitrary :: Gen SimplyTyped')
        describe "System-F" $ do
            followsSimpleType (arbitrary :: Gen SystemF')
            followsPolymorphic (arbitrary :: Gen SystemF')
        describe "System-Fω" $ do
            followsSimpleType (arbitrary :: Gen SystemFOmega')
            followsPolymorphic (arbitrary :: Gen SystemFOmega')
            -- followsHigherOrder (arbitrary :: Gen SystemFOmega')

    unificationRules (arbitrary :: Gen SystemF')

type SimplyTyped' = SimplyTyped AlphabetUpper
type SystemFOmega' = SystemFOmega AlphabetUpper AlphabetLow (Maybe (SimplyTyped AlphabetUpper))
type SystemF' = SF.SystemF AlphabetUpper AlphabetLow

followsSimpleType :: forall t. (SimpleType t, Show t, Arbitrary t) => Gen t -> Spec
followsSimpleType gen = describe "SimpleType laws and properties" $ do
    prop "equivalence is reflexive" $ ((\ !ty -> ty ==== ty) :: t -> Bool)
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
    prop "follows type-ordering rule ((forall a. a) ⊑ _ = True)"
        (typeOrderingRule :: t -> Bool)
    prop "lifts up quantification during abstraction"
        (liftQuantifiersRule :: t -> PolyType t -> Bool)
    prop "Unification rule 1: U(a, b) = V; V(a) ==== V(b)" $
        forAll unifies (uncurry unificationR1)
    prop "Unification rule 2: equivalent type expressions" $
        forAll (uncurry equivalent) (uncurry unificationR1)
    prop "result of 'unify' is commutative" $
        forAll unifies (uncurry unificationCommutative)

    where
        unifies :: (t, t) -> Bool
        unifies (a, b) = not (a ==== b) && isRight (unify a b)

        unificationEquiv :: t -> t -> Bool
        unificationEquiv a b = fromRight False $ do
            u <- unify a b
            return (a ==== b && u a ==== b && u b ==== a)

        unificationR1 :: t -> t -> Bool
        unificationR1 a b = fromRight False $ do
            u <- unify a b
            return (u a ==== u b)

        unificationCommutative :: t -> t -> Bool
        unificationCommutative a b = fromRight False $ do
            u1 <- unify a b
            u2 <- unify b a
            return (u1 a ==== u2 b && u2 a ==== u1 b && u1 a ==== u1 b)

followsHigherOrder :: forall t. (Show t, HigherOrder t, Arbitrary t) => Gen t -> Spec
followsHigherOrder gen = describe "HigherOrder laws and properties" $ do
    prop "follows typeap-untypeap inverse law" $ (typeapInverse ::  t -> t -> Bool)

{-|
    Check that `reify` is the inverse (within a Maybe) of `abstract` (with respect to `equivalent`).
-}
abstractInverse :: (SimpleType t) => t -> t -> Bool
abstractInverse !ta !tb =
    fromMaybe False $ reify (ta /-> tb) >>= (\(ta', tb') -> return (ta ==== ta' && tb ==== tb'))

typeapInverse :: HigherOrder t => t -> t -> Bool
typeapInverse !ta !tb = fmap (uncurry (/$)) (untypeap (ta /$ tb)) == Just (ta /$ tb)

typeOrderingRule :: (Enum e, Polymorphic t, PolyType t ~ e) => t -> Bool
typeOrderingRule !t = poly (toEnum 9999) ⊑ t

{-
    Assert that `abstract` lifts all of the quantifiers to the result.
-}
liftQuantifiersRule :: (Polymorphic t, PolyType t ~ p) => t -> p -> Bool
liftQuantifiersRule t p = t /-> quantify p (poly p) ==== quantify p (t /-> poly p)

disjoint a b = Set.intersection a b == Set.empty

newtype AlphabetLow = AlphabetLow Integer deriving (Eq, Ord, Enum, Data, Typeable)

instance Arbitrary AlphabetLow where
    arbitrary = AlphabetLow <$> elements [0..25]

instance Show AlphabetLow where
    show (AlphabetLow n) = char : if suffix == 0 then
        "" else show suffix where
            suffix = (n - charNum) `div` 26

            charNum = n `mod` 26

            char = cycle ['a'..'z'] !! fromEnum charNum

newtype AlphabetUpper = AlphabetUpper Integer deriving (Eq, Ord, Enum, Data, Typeable)

instance Arbitrary AlphabetUpper where
    arbitrary = AlphabetUpper <$> elements [0..25]

instance Show AlphabetUpper where
    show (AlphabetUpper n) = char : if suffix == 0 then "" else show suffix where
        suffix = (n - charNum) `div` 26

        charNum = n `mod` 26

        char = cycle ['A'..'Z'] !! fromEnum charNum
