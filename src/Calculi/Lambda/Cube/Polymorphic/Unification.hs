{-|
    Module containing functions related to solving and unifying
    polymorphic type expressions.
-}
module Calculi.Lambda.Cube.Polymorphic.Unification (
    -- * Unification related functions
      unify
    , (⊑)
    , (\<)
    , hasSubstitutions
    , applyAllSubs
    , applyAllSubsGr
    , unvalidatedApplyAllSubs
    , resolveMutuals
    -- * Substitution validation
    , substitutionGraph
    , substitutionGraphGr
    , substitutionGraphM
    , topsortSubs
    , topsortSubsG
    , occursCheck
    , conflicts
) where

import           Calculi.Lambda.Cube.Polymorphic
import           Control.Applicative hiding (empty)
import           Control.Lens as Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Bifunctor
import           Data.Either.Combinators
import           Data.Either (partitionEithers)
import           Data.Graph.Inductive as Graph hiding ((&))
import           Data.Graph.Inductive.Helper
import           Data.Function (on)
import           Data.List.Ordered
import           Data.List (groupBy, group, partition)
import           Data.Maybe
import qualified Data.Map                       as Map
import qualified Data.Set                       as Set
import           Data.Tree


{-|
    `substitutions` but takes place in the Unify type.
-}
substitutionsM :: (Polymorphic t, p ~ PolyType t) => t -> t -> Either [SubsErr gr t p] [Substitution t p]
substitutionsM t1 t2 = fmap (uncurry SubsMismatch) `first` substitutions t1 t2

{-
    Get the sequence of substitutions needed to unify two type expressions.

    >>> unify ()
-}
unify :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr)
      => t -> t
      -> Either [SubsErr gr t p] [(t, p)]
unify t1 t2 = do
    -- Find the substitutions and partition them into mutuals and substitutions
    subs <- resolveMutuals <$> substitutionsM t1 t2
    -- validate and order the substitutions
    topsortSubsG <$> substitutionGraph subs

partitionSubstitutions :: [Substitution t p] -> ([(p, p)], [(t, p)])
partitionSubstitutions =
    partitionEithers. fmap (\case (Mutual x y) -> Left (x, y); (Substitution x y) -> Right (x, y);)

{-|
    Test to see if two types have valid substitutions between eachother.
-}
hasSubstitutions :: forall t p. (Polymorphic t, p ~ PolyType t) => t -> t -> Bool
hasSubstitutions t1 t2 = isRight (unify t1 t2 :: Either [SubsErr Gr t p] [(t, p)])

{-|
    Given a list of substitutions, resolve all the mutual substitutions and
    return a list of substitutions in the form @(t, p)@.
-}
resolveMutuals :: forall gr t p. (Polymorphic t, p ~ PolyType t)
               => [Substitution t p] -- ^ The list of substitutions
               -> [(t, p)] -- ^ The resulting list of substitutions
resolveMutuals subs =
    let (mutuals, subs') = filter (uncurry (/=)) `first` partitionSubstitutions subs
    -- As a mutual substitution (a,b) means that a is b, every substitution
    -- of the form (T, a) must be duplicated to include (T, b), and every
    -- substitution of the form (M, b) must be duplicated to include (M, a).
    in (foldr expandMutual subs' mutuals) where
        expandMutual :: (p, p) -> [(t, p)] -> [(t, p)]
        expandMutual (a, b) _subs = do
            -- Get the single substitution
            sub@(term, var) <- _subs
            -- if either a or b are equal to var then
            if a == var || b == var then [(term, a), (term, b)] else return sub

{-|
    Type ordering operator, true if the second argument is more specific or equal to
    the first.

    ===Behaviour

    * A type expression with poly types being ordered against one without them.

        @(∀ a. a) ⊑ (X → Y) = True@

    * A type expression being ordered against itself, displaying reflexivity.

        @(X → X) ⊑ (X → X) = True@

    * All type expressions are more specific than a type expression
      of just a single (bound or unbound) poly type.

        @(a) ⊑ (a) = True@

        @(a) ⊑ (b) = True@

        @(a) ⊑ (X) = True@

        @(a) ⊑ (X → Y) = True@

        etc.
-}
(⊑) :: (Polymorphic t, p ~ PolyType t) => t -> t -> Bool
t ⊑ t' = fromRight False $ do
    subs <- resolveMutuals <$> substitutionsM t' t
    applySubs <- applyAllSubsGr subs
    return (t' ≣ applySubs t)

infix 4 ⊑

{-|
    Non-unicode @⊑@.
-}
(\<) :: (Polymorphic t, p ~ PolyType t) => t -> t -> Bool
(\<) = (⊑)

infix 4 \<

{-|
    For a given list of substitutions, either find and report inconsistencies
    through `SubsErr` or compute a topsort by order of substitution such that for
    a list of substitutions @[a, b, c]@ c should be applied, then b, then a.

    This backward application is a product of how the graph used to compute
    the reordering is notated and how topsorting is ordered. In this
    graph for nodes @N, M@ and egde label @p@, @N --p-> M@ notates that
    all instances of @p@ in @M@ will be substituted by @N@. In regular topsort
    this means that @N@ will preceed @M@ in the list, but this doesn't make sense
    when we topsort to tuples of the form @(N, p)@.
-}
topsortSubs :: forall gr t p. (DynGraph gr, Polymorphic t, p ~ PolyType t)
            => [(t, p)]
            -> Either [SubsErr gr t p] [(t, p)]
topsortSubs = fmap topsortSubsG . (substitutionGraph :: [(t, p)] -> Either [SubsErr gr t p] (gr t p))

{-|
    A version of `topsortSubs` that takes an already generated graph rather than
    building it's own.

    If given a graph with cycles or nodes with 2 or more inward edges of the same label
    then there's no garuntee that the substitutions will be applied correctly.
-}
topsortSubsG :: forall gr t p. (Graph gr)
             => gr t p
             -> [(t, p)]
topsortSubsG = unvalidatedEdgeyTopsort
{-|
    Without validating if the substitutions are consistent, fold them into a single
    function that applies all substitutions to a given type expression.
-}
unvalidatedApplyAllSubs :: (Polymorphic t, p ~ PolyType t)
                        => [(t, p)]
                        -> t
                        -> t
unvalidatedApplyAllSubs = foldr (\sub f -> uncurry applySubstitution sub . f) id

{-|
    Validate substitutions and fold them into a single substitution function.
-}
applyAllSubs :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr)
             => [(t, p)]
             -> Either [SubsErr gr t p] (t -> t)
applyAllSubs = fmap unvalidatedApplyAllSubs . topsortSubs

{-|
    `applyAllSubs` using fgl's `Gr`.
-}
applyAllSubsGr :: (Polymorphic t, p ~ PolyType t)
               => [(t, p)]
               -> Either [SubsErr Gr t p] (t -> t)
applyAllSubsGr = applyAllSubs

{-|
    Function that builds a graph representing valid substitutions or reports
    any part of the graph's structure that would make the substitutions invalid.
-}
substitutionGraph
    :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr)
    => [(t, p)]
    -> Either [SubsErr gr t p] (gr t p)
substitutionGraph subs =
    let (errs, (_, graph :: gr t p)) = run empty (substitutionGraphM subs)
    in if null errs then Right graph else Left errs

{-|
    `substitutionGraph` using fgl's `Gr`.
-}
substitutionGraphGr :: forall t p. (Polymorphic t, p ~ PolyType t)
              => [(t,p)]
              -> Either [SubsErr Gr t p] (Gr t p)
substitutionGraphGr = substitutionGraph

{-|
    A version of `substitutionGraph` that works within fgl's NodeMap state monad.
-}
substitutionGraphM
    :: forall t p gr. -- No haddock documentation for constraints, but putting this here anyway
    ( Polymorphic t   -- The typesystem @t@ is a an instance of Polymorphic
    , p ~ PolyType t  -- @p@ is @t@'s representation of type variables
    , Ord p           -- t's representation of type variables is ordered
    , DynGraph gr     -- the graph representation is an instance of DynGraph
    )
    => [(t, p)]       -- ^ A list of substitutions
    -> NodeMapM t p gr [SubsErr gr t p]
                      -- ^ A nodemap monadic action where the graph's edges are substitutions
                      -- and the nodes are type expressions.
substitutionGraphM subs = do
    {-
        Construct the graph so we have something to work with.
    -}
    -- Assemble a list of all the type expressions, including the substitution targets
    {- Note: to make this work from a point of theory, all the targets in "subs" are turned into
       type expressions using the polymorphic constructor, allowing all substitutions to
       have at least one edge from the substitutions to the targets. -}
    let typeExprs = nubSort $ concat ((\(t, p) -> [t, poly p]) <$> subs)
    -- Build a list of type expressions and their bases.
    let basesList = (\t -> (t, freeTypeVariables t)) <$> typeExprs
    -- Construct the edges
    let subsEdges = buildEdge <$> subs <*> basesList
    -- Insert the nodes. (crashes if this isn't done first, because fgl!)
    void (insMapNodesM typeExprs)
    -- Insert the edges.
    insMapEdgesM (catMaybes subsEdges)
    -- Compute and return the errors
    gets (occursCheck . snd) where
        {-
            Given a substitution pair and pair of a type expression and it's
            base types, check if the substitution's own target appears in those
            base types.
        -}
        buildEdge :: (t, p) -> (t, Set.Set t) -> Maybe (t, t, p)
        buildEdge (t1, p) (t2, t2'bases)
            | poly p `Set.member` t2'bases = Just (t1, t2, p)
            | otherwise = Nothing

{-|
    From a graph representing substitutions of variables @p@ in terms @t@, where
    edges represent the origin node replacing the variable represented by the edge label
    in the target node.

    e.g. The edge @(N, (x -> x), x)@ corresponds to replacing all instances of the variable @x@ in
    @(x -> x)@ with @N@.
-}
occursCheck :: forall gr t p. (DynGraph gr, Ord p, Ord t) => gr t p -> [SubsErr gr t p]
occursCheck graph =
    let cycles = cyclicSubgraphs graph
        clashes = clashesOfGraph graph
    in if not (null cycles) then
        -- If ther are cycles, return them after passing them through the error constructor.
        CyclicSubstitution <$> cycles
        else if not (null clashes) then
            MultipleSubstitutions <$> clashes
            else [] where
        {-
            Generate a list of trees of fully labelled edges,
        -}
        clashesOfGraph :: gr t p -> [ConflictTree t p]
        clashesOfGraph graph =
            uncurry (branchConflicts graph) <$> conflicts graph

{-|
    Find all contexts with non-unique inward labels, paired with each
    label that wasn't unique.
-}
conflicts :: (DynGraph gr, Ord p, Ord t) => gr t p -> [(p, Graph.Context t p)]
conflicts graph = do
    -- For each node in the graph...
    node <- nodes graph
    --Find it's inward edges and group them by label, filtering any label that appears once.
    conflict <- nub =<< filter hasSome (group (inn graph node <&> (^._3)))
    return (conflict, context graph node)

{-|
    Given a graph, a conflicting label, and the node where the label is conflicting;
    branch out towards it's roots.
-}
branchConflicts :: (DynGraph gr, Ord p, Ord t) => gr t p -> p -> Graph.Context t p -> ([Tree (t, [p])], t)
branchConflicts graph lbl ctx@(_,nn,nl,_) = flip (,) nl $ do
    -- Get all the inward edges
    let inward = filter ((== lbl) . (^._3)) (inn graph nn)
    -- Reverse depth-first search to find all the roots, using the contexts
    -- as the tree's value.
    tree <- rdffWith id ((^._1) <$> inward) graph
    -- process the tree,
    return $ processTree ctx tree where
        processTree :: Graph.Context t p -> Tree (Graph.Context t p) -> Tree (t, [p])
        processTree pctx (Node ctx forest) =
            Node (lab' ctx, fst <$> filter ((== node' pctx) . snd) (ctx^._4)) (processTree ctx <$> forest)
