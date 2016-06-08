{-# LANGUAGE BangPatterns #-}
import           Calculi.Lambda
import           Calculi.Lambda.Cube
import           Calculi.Lambda.Cube.Systems.SimplyTyped  as ST
import           Calculi.Lambda.Cube.Systems.SystemF      as SF
import           Calculi.Lambda.Cube.Systems.SystemFOmega as SFO
import           Data.Maybe
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
                followsHigherOrder (arbitrary :: Gen SystemFOmega')

type SimplyTyped' = SimplyTyped Integer
type SystemFOmega' = SystemFOmega Integer Integer
type SystemF' = SF.SystemF Integer Integer

followsSimpleType :: (SimpleType t) => Gen t -> Spec
followsSimpleType gen = describe "SimpleType laws and properties" $
    prop "follows abstract-reify inverse law" $ abstractInverse <$> gen <*> gen

followsPolymorphic :: forall t. (Polymorphic t, Show t, Arbitrary t, PolyType t ~ Integer) => Gen t -> Spec
followsPolymorphic gen = describe "Polymorphic laws and properties" $ do
    prop "equivalence is reflexive" $
        (\ !ty -> ty ≣ ty) <$> gen
    prop "substitution is reflexive" $
        (\ !ty -> ty `canSubstitute` ty) <$> gen
    prop "follows quantify-unquantify inverse law" $ quantifyInverse <$> arbitrary <*> gen
    prop "follows type-ordering rule 1" (typeOrderingRule :: t -> Bool)

followsHigherOrder :: (HigherOrder t) => Gen t -> Spec
followsHigherOrder gen = describe "HigherOrder laws and properties" $ do
    prop "follows kind-unkind inverse law" $
        (\ty -> unkind (kind ty) == Just ty) <$> gen
    prop "follows typeap-untypeap inverse law" $ typeapInverse <$> gen <*> gen

{-|
    An expression of type "(0 -> 5) -> 0 -> 5"
-}
expr1 :: LambdaExpr Integer (SimplyTyped Integer)
expr1 = Lambda (1, ST.Mono 0 /-> ST.Mono 5) (Lambda (2, ST.Mono 0) (Var 1 `Apply` Var 2))

{-|
    Check that `reify` is the inverse (within a Maybe) of `abstract`.
-}
abstractInverse :: (SimpleType t) => t -> t -> Bool
abstractInverse !ta !tb = fmap (uncurry (/->)) (reify (ta /-> tb)) == Just (ta /-> tb)

quantifyInverse :: (Polymorphic t, PolyType t ~ Integer) => Integer -> t -> Bool
quantifyInverse !ta !tb = fmap (uncurry quantify) (unquantify (quantify ta tb)) == Just (quantify ta tb)

typeapInverse :: HigherOrder t => t -> t -> Bool
typeapInverse !ta !tb = fmap (uncurry (/$)) (untypeap (ta /$ tb)) == Just (ta /$ tb)

typeOrderingRule :: (Polymorphic t, PolyType t ~ Integer) => t -> Bool
typeOrderingRule t = t \< poly 900000
