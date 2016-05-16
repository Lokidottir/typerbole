
import Calculi.Lambda
import qualified Data.Set as Set
import qualified Data.Map as Map
import Calculi.Lambda.Cube
import Calculi.Lambda.Cube.Systems.SimplyTyped as ST
import Test.QuickCheck
import Test.Hspec
import Data.Bifoldable
import Data.Monoid
import Data.Maybe
import Control.Monad

main :: IO ()
main = do
    qcSucess <- runTests
    when qcSucess . hspec $ do
        it "Typechecks simply-typed lambda calculus" $
            typecheckSTLC defaultSTReporter (envFromExpr expr1) expr1
                `shouldBe` Right ((ST.Mono 0 /-> ST.Mono 5) /-> ST.Mono 0 /-> ST.Mono 5)

{-|
    An expression of type "(0 -> 5) -> 0 -> 5"
-}
expr1 :: LambdaExpr Integer (SimplyTyped Integer)
expr1 = Lambda (1, ST.Mono 0 /-> ST.Mono 5) (Lambda (2, ST.Mono 0) (Var 1 `Apply` Var 2))

{-|
    Check that `reify` is the inverse (within a Maybe) of `abstract`.
-}
abstractInverse :: (SimpleType t) => t -> Bool
abstractInverse t | isJust (reify t) = fmap (uncurry abstract) (reify t) /= Just t
                       | otherwise = False

prop_abstractInverseST :: SimplyTyped Integer -> Bool
prop_abstractInverseST = abstractInverse

runTests = $quickCheckAll
