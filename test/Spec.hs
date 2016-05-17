
import Calculi.Lambda
import Calculi.Lambda.Cube
import Calculi.Lambda.Cube.Systems.SimplyTyped as ST
import Calculi.Lambda.Cube.Systems.SystemFOmega as SFO
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Data.Maybe



main :: IO ()
main = hspec $ do
        describe "SimplyTyped" $
            followsSimpleType (arbitrary :: Gen SimplyTyped')
        describe "System-Fω" $ do
            followsSimpleType (arbitrary :: Gen SystemFOmega')
            followsPolymorphic (arbitrary :: Gen SystemFOmega')


type SimplyTyped' = SimplyTyped Integer
type SystemFOmega' = SystemFOmega Integer Integer

followsSimpleType :: forall t. (SimpleType t) => Gen t -> Spec
followsSimpleType gen =
    prop "follows abstract-reify inverse law" $ abstractInverse <$> gen <*> gen

followsPolymorphic :: forall t. (Polymorphic t) => Gen t -> Spec
followsPolymorphic gen = do
    prop "equivalence is reflexive" $ do
        ty <- gen
        return (ty ≣ ty)
    prop "substitution is reflexive" $ do
        ty <- gen
        return (ty `canSubstitute` ty)

{-|
    An expression of type "(0 -> 5) -> 0 -> 5"
-}
expr1 :: LambdaExpr Integer (SimplyTyped Integer)
expr1 = Lambda (1, ST.Mono 0 /-> ST.Mono 5) (Lambda (2, ST.Mono 0) (Var 1 `Apply` Var 2))

{-|
    Check that `reify` is the inverse (within a Maybe) of `abstract`.
-}
abstractInverse :: (SimpleType t) => t -> t -> Bool
abstractInverse ta tb = fmap (uncurry abstract) (reify (ta /-> tb)) == Just (ta /-> tb)
