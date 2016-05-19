module Calculi.Lambda where

import           Data.Bifunctor.TH
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
    A simple lambda calculus AST with Let expressions.
-}
data LambdaExpr v t =
      Var v                                   -- ^ A reference to a variable
    | Let [LetDeclr v t] (LambdaExpr v t)     -- ^ A let expression
    | Apply (LambdaExpr v t) (LambdaExpr v t) -- ^ An application of one expression to another
    | Lambda (v, t) (LambdaExpr v t)          -- ^ A varexpr and a function body
    deriving (Eq, Ord, Show, Data)

type LetDeclr v t = ((v, t), LambdaExpr v t)

deriveBifunctor ''LambdaExpr
deriveBifoldable ''LambdaExpr
deriveBitraversable ''LambdaExpr

instance (Arbitrary v, Data v, Arbitrary t, Data t) => Arbitrary (LambdaExpr v t) where
    -- TODO: Remove the instances of Data for v and t
    arbitrary = sized generatorP

type UntypedLambdaExpr v = LambdaExpr v ()

{-|
    Given the contents of a let expression's declarations, generate a graph
    showing the dependencies between each declaration, including recursion
    as loops.
-}
letsDependency :: (DynGraph gr, Ord v, Ord t) => [LetDeclr v t] -> gr (LetDeclr v t) ()
letsDependency = snd . letsDependency'

{-|
    `letsDependency` but also return the internally used NodeMap.
-}
letsDependency' :: forall v t gr. (DynGraph gr, Ord v, Ord t) => [LetDeclr v t] -> (NodeMap (LetDeclr v t), gr (LetDeclr v t) ())
letsDependency' lets =
    let
        declrs = fst . fst <$> lets
        declrsSet = Set.fromList declrs
        -- memoize because we need to check the vars then use the entire declaration and this
        -- is very costly.
        declrMap :: Map.Map v (LetDeclr v t)
        declrMap = Map.fromList $ zip declrs lets

        {-
            Get the intersection of the free variables in the expression and the set of
            declarations in this let expression.
        -}
        dependsOf :: LetDeclr v t -> Set.Set v
        dependsOf = Set.intersection declrsSet . freeVars . snd

        {-
            Find all the inward nodes of a declaration.
        -}
        inwardNodes :: LetDeclr v t -> [LetDeclr v t]
        inwardNodes declr =
            fromMaybe [] (sequence $ (`Map.lookup` declrMap) <$> Set.toList (dependsOf declr))

        inwardEdges :: LetDeclr v t -> [(LetDeclr v t, LetDeclr v t, ())]
        inwardEdges declr = (\inward -> (inward, declr, ())) <$> inwardNodes declr
    in snd . run empty $ insMapEdgesM (concat $ inwardEdges <$> lets)

{-|
    For a given expression, attempt to convert the let expressions into lambda
    expressions. Any let expressions left over after this conversion would be
    the result of cycles in those let expressions.
-}
deepUnlet :: (Ord v, Ord t) => LambdaExpr v t -> LambdaExpr v t
deepUnlet = \case
    var@(Var _)    -> var
    Let lets expr  -> unlet lets (deepUnlet expr)
    Apply fun arg  -> Apply (deepUnlet fun) (deepUnlet arg)
    Lambda vt expr -> Lambda vt (deepUnlet expr)

{-|
    Unlet the content of a single let expression, not recursing on the let's
    body.
-}
unlet :: forall v t.
       (Ord v, Ord t)
    => [LetDeclr v t] -- ^ The list of declarations in a let expression
    -> LambdaExpr v t -- ^ The let expression's body
    -> LambdaExpr v t -- ^ The final expression with the same or fewer let expressions
unlet lets expr =
    let -- Build the dependency graph
        depends :: Gr (LetDeclr v t) () = letsDependency lets
        -- Get the regular topsort.
        tsorted            = topsortWithCycles depends
        -- This is what turns the cycles found in tsorted
        -- to let expressions and the non-cycle nodes into
        -- lambda-apply name scoping.
        unlet' val lexpr  = case val of
            -- A cycle appears, turn it back into a Let
            Left cy     -> Let cy lexpr
            -- A declaration appears, name the body of the declaration using
            -- a lambda expression instead. e.g. ((\x -> x) y) names y as x.
            Right (declr, body) -> Lambda declr lexpr `Apply` body
    in foldr unlet' expr tsorted

{-|
    Find all the unbound variables in an expression.
-}
freeVars :: Ord v => LambdaExpr v t -> Set.Set v
freeVars = \case
    Var v              -> Set.singleton v
    Let lets expr      ->
        -- Combine all the free variables from the declared variables
        -- and the let's target expression before removing all declared
        -- variables from the set.
        Set.difference
            (mconcat $ freeVars expr : (freeVars . snd <$> lets))
            (Set.fromList (fst . fst <$> lets))
    Apply fun arg      ->
        -- Union the free variables of both parts of the Apply
        freeVars fun <> freeVars arg
    Lambda (v, _) expr ->
        -- remove the variable defined by the lambda from the set of free
        -- variables found in the body.
        Set.delete v (freeVars expr)
