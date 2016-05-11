module Calculi.Lambda where

import           Data.Bifoldable
import           Data.Bifunctor
import qualified Data.Generics as Generics
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Helper
import qualified Data.Set                    as Set
import qualified Data.Map                    as Map
import           Data.Semigroup
import           Data.Maybe

{-|
    A simple lambda calculus AST with Let expressions.
-}
data LambdaExpr v t =
      Var v                                   -- ^ A reference to a variable
    | Let [LetDeclr v t] (LambdaExpr v t)     -- ^ A let expression
    | Apply (LambdaExpr v t) (LambdaExpr v t) -- ^ An application of one expression to another
    | Lambda (v, t) (LambdaExpr v t)          -- ^ A varexpr and a function body
    deriving (Eq, Ord, Show, Generics.Typeable, Generics.Data)

type LetDeclr v t = ((v, t), LambdaExpr v t)

type UntypedLambdaExpr v = LambdaExpr v ()

instance Bifunctor LambdaExpr where
    bimap f g lx = case lx of
        Var v               -> Var (f v)
        Let lets expr       -> Let (bimap (bimap f g) (bimap f g) <$> lets) (bimap f g expr)
        Apply fun arg       -> Apply (bimap f g fun) (bimap f g arg)
        Lambda constrs expr -> Lambda (bimap f g constrs) (bimap f g expr)

instance Bifoldable LambdaExpr where
    bifoldr f g z lx = case lx of
        Var v               -> f v z
        Let lets expr       ->
            bifoldr f g (foldr (\(declr, lexpr) st -> bifoldr f g (bifoldr f g st lexpr) declr) z lets) expr
        Apply fun arg       -> bifoldr f g (bifoldr f g z arg) fun
        Lambda constrs expr -> bifoldr f g (bifoldr f g z expr) constrs

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
    -> LambdaExpr v t
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
