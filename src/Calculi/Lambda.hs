{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Calculi.Lambda (
      -- * Typed Lambda Calculus AST.
      LambdaTerm(..)
    , UntypedLambdaTerm
      -- ** Analysis Helpers
    , freeVars
      -- ** Name-related errors
    , NotKnownErr(..)
      -- * Let declaration helpers
    , LetDeclr
    , unlet
    , letsDependency
    , letsDependency'
) where

import           Data.Bifunctor.TH
import           Data.Bifunctor (second)
import           Data.Either.Combinators
import           Data.Either (lefts, partitionEithers)
import           Data.Generics (Data(..))
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Helper
import qualified Data.Map                    as Map
import           Data.Maybe
import           Generic.Random.Data
import           Data.Semigroup
import qualified Data.Set                    as Set
import           Test.QuickCheck

{-|
    A simple, typed lambda calculus AST with constants.
-}
data LambdaTerm c v t =
      Variable v
      -- ^ A reference to a variable.
    | Constant c
      -- ^ A constant value, such as literals or constructors.
    | Apply (LambdaTerm c v t) (LambdaTerm c v t)
      -- ^ An application of one expression to another.
    | Lambda (v, t) (LambdaTerm c v t)
      -- ^ A lambda expression, with a variable definition and
      -- a function body.
    deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

deriveBifunctor ''LambdaTerm
deriveBifoldable ''LambdaTerm
deriveBitraversable ''LambdaTerm

instance (Arbitrary c, Data c,
          Arbitrary v, Data v,
          Arbitrary t, Data t) => Arbitrary (LambdaTerm c v t) where
    arbitrary = sized generatorSR

type LetDeclr c v t = ((v, t), LambdaTerm c v t)

type UntypedLambdaTerm c v = LambdaTerm c v ()

{-|
    Name-related errors, for when there's a variable, type or constant
    that doesn't appear in the environment that was given to the typechecker.
-}
data NotKnownErr c v t =
      UnknownType t
    -- ^ A type appears that is not in scope
    | UnknownVariable v
    -- ^ A variable appears that is not in scope
    | UnknownConstant c
    -- ^ A constant appears that is not in scope
    deriving (Eq, Ord, Show)

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
        unlet' (declr, body) lexpr = Lambda declr lexpr `Apply` body
    in if null cycles then Right (foldr unlet' expr lets') else Left cycles

{-|
    Find all the unbound variables in an expression.
-}
freeVars :: Ord v => LambdaTerm c v t -> Set.Set v
freeVars = \case
    Variable v          -> Set.singleton v
    Constant _          -> Set.empty
    Apply fun arg      ->
        -- Union the free variables of both parts of the Apply
        freeVars fun <> freeVars arg
    Lambda (v, _) expr ->
        -- remove the variable defined by the lambda from the set of free
        -- variables found in the body.
        Set.delete v (freeVars expr)
