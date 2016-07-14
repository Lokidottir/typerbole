module Calculi.Lambda (
      -- * Typed Lambda Calculus AST.
      LambdaExpr(..)
    , LambdaTerm(..)
    , UntypedLambdaExpr
      -- ** Analysis Helpers
    , freeVars
      -- * Let declaration helpers
    , LetDeclr
    , unlet
    , letsDependency
    , letsDependency'
) where

import           Data.Bifunctor.TH
import           Data.Either.Combinators
import           Data.Either (lefts, partitionEithers)
import           Data.Generics (Data(..))
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Helper
import qualified Data.Map                    as Map
import           Data.Maybe
import           Data.Random.Generics
import           Data.Semigroup
import qualified Data.Set                    as Set
import           Test.QuickCheck

{-|
    A simple typed lambda calculus AST.
-}
data LambdaExpr v t =
      Var v                                   -- ^ A reference to a variable
    | Apply (LambdaExpr v t) (LambdaExpr v t) -- ^ An application of one expression to another
    | Lambda (v, t) (LambdaExpr v t)          -- ^ A variable definition and a function body
    deriving (Eq, Ord, Show, Data)

deriveBifunctor ''LambdaExpr
deriveBifoldable ''LambdaExpr
deriveBitraversable ''LambdaExpr

instance (Arbitrary v, Data v, Arbitrary t, Data t) => Arbitrary (LambdaExpr v t) where
    -- TODO: Remove the instances of Data for v and t
    arbitrary = sized generatorP

type UntypedLambdaExpr v = LambdaExpr v ()

{-|
    A simple, typed lambda calculus AST with constants.
-}
data LambdaTerm c v t =
      Variable v
      -- ^ A reference to a variable.
    | Constant c
      -- ^ A constant value, such as @""@.
    | Apply_ (LambdaTerm c v t) (LambdaTerm c v t)
      -- ^ An application of one expression to another.
    | Lambda_ (v, t) (LambdaTerm c v t)
      -- ^ A lambda expression, with a variable definition and
      -- a function body.
    deriving (Eq, Ord, Show, Data)

deriveBifunctor ''LambdaTerm
deriveBifoldable ''LambdaTerm
deriveBitraversable ''LambdaTerm

instance (Arbitrary c, Data c,
          Arbitrary v, Data v,
          Arbitrary t, Data t) => Arbitrary (LambdaTerm c v t) where
    arbitrary = sized generatorSR

type LetDeclr c v t = ((v, t), LambdaTerm c v t)

{-|
    Given the contents of a let expression's declarations, generate a graph
    showing the dependencies between each declaration, including recursion
    as loops.
-}
letsDependency :: (DynGraph gr, Ord c, Ord v, Ord t) => [LetDeclr c v t] -> gr (LetDeclr c v t) ()
letsDependency = snd . letsDependency'

{-|
    `letsDependency` but also return the internally used NodeMap.
-}
letsDependency' :: forall gr c v t. (DynGraph gr, Ord c, Ord v, Ord t)
                => [LetDeclr c v t]
                -> (NodeMap (LetDeclr c v t), gr (LetDeclr c v t) ())
letsDependency' lets =
    let
        declrs = fst . fst <$> lets
        declrsSet = Set.fromList declrs
        -- memoize because we need to check the vars then use the entire declaration and this
        -- is very costly.
        declrMap :: Map.Map v (LetDeclr c v t)
        declrMap = Map.fromList $ zip declrs lets

        {-
            Get the intersection of the free variables in the expression and the set of
            declarations in this let expression.
        -}
        dependsOf :: LetDeclr c v t -> Set.Set v
        dependsOf = Set.intersection declrsSet . freeVars . snd

        {-
            Find all the inward nodes of a declaration.
        -}
        inwardNodes :: LetDeclr c v t -> [LetDeclr c v t]
        inwardNodes declr =
            fromMaybe [] (sequence $ (`Map.lookup` declrMap) <$> Set.toList (dependsOf declr))

        inwardEdges :: LetDeclr c v t -> [(LetDeclr c v t, LetDeclr c v t, ())]
        inwardEdges declr = (\inward -> (inward, declr, ())) <$> inwardNodes declr
    in snd . run empty $ insMapEdgesM (concat $ inwardEdges <$> lets)

{-|
    Unlet non-cyclic let expressions.
-}
unlet :: forall c v t. (Ord c, Ord v, Ord t)
      => [LetDeclr c v t] -- ^ The list of declarations in a let expression
      -> LambdaTerm c v t -- ^ The body of the let declaration
      -> Either [[LetDeclr c v t]]
                (LambdaTerm c v t) -- ^ Either a list of cyclic lets or the final expression
unlet lets expr =
    let -- Build the dependency graph
        depends :: Gr (LetDeclr c v t) () = letsDependency lets
        -- Get the regular topsort.
        tsorted            = topsortWithCycles depends
        (cycles, lets')    = partitionEithers tsorted
        -- This is what turns the cycles found in tsorted
        -- to let expressions and the non-cycle nodes into
        -- lambda-apply name scoping.
        unlet' (declr, body) lexpr = Lambda_ declr lexpr `Apply_` body
    in if null cycles then Right (foldr unlet' expr lets') else Left cycles

{-|
    Find all the unbound variables in an expression.
-}
freeVars :: Ord v => LambdaTerm c v t -> Set.Set v
freeVars = \case
    Variable v          -> Set.singleton v
    Constant _          -> Set.empty
    Apply_ fun arg      ->
        -- Union the free variables of both parts of the Apply
        freeVars fun <> freeVars arg
    Lambda_ (v, _) expr ->
        -- remove the variable defined by the lambda from the set of free
        -- variables found in the body.
        Set.delete v (freeVars expr)
