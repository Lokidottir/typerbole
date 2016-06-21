{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
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
    , resolveMutuals
    -- * Unification type
    , Unify(..)
    , runUnify
    , runUnify'
    , newPolyType
    -- ** Unification type's state
    , UnifyState(..)
    , tapeOfNewPolyTypes
    -- * Substitution validation
    , substitutionGraph
    , substitutionGraphGr
    , substitutionGraphM

) where

import           Calculi.Lambda.Cube.Polymorphic
import           Control.Applicative hiding (empty)
import           Control.Lens as Lens hiding ((&))
import qualified Control.Lens as Lens ((&))
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Bifunctor
import           Data.Either.Combinators
import           Data.Either (partitionEithers)
import           Data.Graph.Inductive as Graph
import           Data.Graph.Inductive.Helper
import           Data.List.Ordered
import           Data.List (groupBy, partition)
import           Data.Maybe
import qualified Data.Set                       as Set
import           Data.Tree

data UnifyState t p = UnifyState {
    _tapeOfNewPolyTypes :: [p]
} deriving (Eq, Ord, Show)

makeLenses ''UnifyState

{-|
    State and Error type for solving unification. In a newtype to
    make typeerrors more readable.
-}
newtype Unify t p a = Unify {
    unifyToTranformers :: ExceptT [SubsErr Gr t p] (State (UnifyState t p)) a
} deriving (
             Functor
           , Applicative
           , Alternative
           , Monad
           , MonadState (UnifyState t p)
           , MonadError [SubsErr Gr t p]
           , MonadPlus
           )

{-|
    Run a unification action.
-}
runUnify :: UnifyState t p -> Unify t p a -> Either [SubsErr Gr t p] (a, UnifyState t p)
runUnify st action =
    (\(errs, st') -> flip (,) st' <$> errs) . flip runState st $ runExceptT (unifyToTranformers action)

{-|
    `runUnify`, discarding the final state.
-}
runUnify' :: UnifyState t p -> Unify t p a -> Either [SubsErr Gr t p] a
runUnify' st action = fmap fst (runUnify st action)

{-|
    Pulls a new poly type from the infinite list
-}
newPolyType :: Unify t p p
newPolyType = do
    -- get the variable at the head of the list
    v <- head <$> use tapeOfNewPolyTypes
    -- set the list to be to tail of what it is now so
    -- the variable we just got isn't returned again.
    tapeOfNewPolyTypes %= tail
    -- return the variable
    return v

{-|
    `substitutions` but takes place in the Unify type.
-}
substitutionsM :: (Polymorphic t, p ~ PolyType t) => t -> t -> Unify t p [Substitution t p]
substitutionsM t1 t2 = eitherToError $ fmap (uncurry SubsMismatch) `first` substitutions t1 t2

unify :: forall t p. (Polymorphic t, p ~ PolyType t) => t -> t -> Unify t p [(t, p)]
unify t1 t2 = do
    -- Find the substitutions and partition them into mutuals and substitutions
    subs <- resolveMutuals =<< substitutionsM t1 t2
    -- validate and order the substitutions
    eitherToError (topsortSubsG <$> substitutionGraphGr subs)

partitionSubstitutions :: [Substitution t p] -> ([(p, p)], [(t, p)])
partitionSubstitutions =
    partitionEithers. fmap (\case (Mutual x y) -> Left (x, y); (Substitution x y) -> Right (x, y);)

{-|
    Test to see if two types have valid substitutions between eachother.
-}
hasSubstitutions :: (Polymorphic t, p ~ PolyType t) => t -> t -> Unify t p Bool
hasSubstitutions t1 t2 =
    -- Run a unification action with the current state, converting errors into False
    -- and a successful unification into a True.
    gets (\st -> isRight (runUnify st (unify t1 t2)))

{-|
    Given a list of substitutions, resolve all the mutual substitutions and
    return a list of substitutions in the form @(t, p)@.
-}
resolveMutuals :: forall t p. (Polymorphic t, p ~ PolyType t) => [Substitution t p] -> Unify t p [(t, p)]
resolveMutuals subs = do
    let (mutuals, subs') = filter (uncurry (/=)) `first` partitionSubstitutions subs
    -- As a mutual substitution (a,b) means that a is b, every substitution
    -- of the form (T, a) must be duplicated to include (T, b), and every
    -- substitution of the form (M, b) must be duplicated to include (M, a).
    return (foldr expandMutual subs' mutuals) where
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

    __NOTE:__ These examples occur within the Unify type, and must be put through a runUnify
    function before the results can be computed.

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
(⊑) :: (Polymorphic t, p ~ PolyType t) => t -> t -> Unify t p Bool
t ⊑ t' = gets $ \st -> fromRight False . runUnify' st $ do
    subs <- resolveMutuals =<< substitutionsM t' t
    applySubs <- eitherToError (applyAllSubs subs)
    return (t' ≣ applySubs t)

infix 4 ⊑

{-|
    Non-unicode @⊑@.
-}
(\<) :: (Polymorphic t, p ~ PolyType t) => t -> t -> Unify t p Bool
(\<) = (⊑)

infix 4 \<

---------------- Taken From the original Polymorphic module ----------------

{-|
    Unify two type expressions.
-}
unify' :: forall gr t p. (Polymorphic t, DynGraph gr, PolyType t ~ p)
      => [p]          -- ^ An infinite list of type variables that don't exist in either type expressions
                      -- or a greater typing context.
      -> t            -- ^ The first type expression.
      -> t            -- ^ The second type expression.
      -> Either [SubsErr gr t p] ([p], [(t, p)])
                      -- ^ The result, either substitution errors or a tuple of the remaining
                      -- poly types in the infinte list and the
unify' tape t1 t2 = do
    -- Get the substitutions, turn any mismatches into SubsErrs.
    subs <- fmap (uncurry SubsMismatch) `first` substitutions t1 t2
    let (tapeRemainder, subs') = resolveMutuals tape subs
    validSubs <- topsortSubs subs'
    return (tapeRemainder, validSubs) where
        {-
            With an infinite tape, turn all `Mutual` substitutions into
            substitutions of the form (t, p), consuming poly types from
            the infinite list when they're needed to solve mutual substitutions.

            NOTE: May need to rethink how Mutual is structured, there's a massive chance that
                  that the structure may lead to cycles or clashes that are entirely
                  composed of poly types that could be solved with a version of this
                  that tackles mutual substitution of any number of poly types.

                  tl;dr: make Mutual have a list of mutuals instead, put the burden of checking
                         this put on the implementer of the typesystems.
        -}
        resolveMutuals :: [p] -> [Substitution t p] -> ([p], [(t, p)])
        resolveMutuals _tape = foldl resolveSingle (_tape, []) where
            {-
                When encountering a Mutual, consume a poly type from
                the infinte list, otherwise just convert the substitution
                into a tuple and pass the list on.
            -}
            resolveSingle :: ([p], [(t, p)])
                          -> Substitution t p
                          -> ([p], [(t, p)])
            resolveSingle (h : tl, subs) (Mutual p1 p2)            = (tl , (poly h, p1) : (poly h, p2) : subs)
            resolveSingle (_tape, subs) (Substitution expr target) = (_tape , (expr, target) : subs)

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
topsortSubs :: forall gr t p. (DynGraph gr, Polymorphic t, p ~ PolyType t) => [(t, p)] -> Either [SubsErr gr t p] [(t, p)]
topsortSubs = fmap topsortSubsG . (substitutionGraph :: [(t, p)] -> Either [SubsErr gr t p] (gr t p))

{-|
    A version of `topsortSubs` that takes an already generated graph rather than
    building it's own.

    If given a graph with cycles or nodes with 2 or more inward edges of the same label
    then there's no garuntee that the substitutions will be applied correctly.
-}
topsortSubsG :: forall gr t p. (Graph gr) => gr t p -> [(t, p)]
topsortSubsG = unvalidatedEdgeyTopsort
{-|
    Without validating if the substitutions are consistent, fold them into a single
    function that applies all substitutions to a given type expression.
-}
unvalidatedApplyAllSubs :: (Polymorphic t, p ~ PolyType t) => [(t, p)] -> t -> t
unvalidatedApplyAllSubs = foldr (\sub f -> uncurry applySubstitution sub . f) id

{-|
    Validate substitutions and fold them into a single substitution function.
-}
applyAllSubs :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr) => [(t, p)] -> Either [SubsErr gr t p] (t -> t)
applyAllSubs = fmap unvalidatedApplyAllSubs . topsortSubs

applyAllSubsGr :: (Polymorphic t, p ~ PolyType t) => [(t, p)] -> Either [SubsErr Gr t p] (t -> t)
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
    occursCheck <$> gets snd where
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
        clashesOfGraph :: gr t p -> [ClashTreeRoot t p]
        clashesOfGraph graph = concatMap findClashRootPaths candidates where

            {-
                Group by equality on the first element (edge label) and inequality on the second.
            -}
            groupByEdgelabel :: (Eq a, Eq b) => [(a, b)] -> [[(a, b)]]
            groupByEdgelabel = groupBy (\(a, b) (a', b') -> a == a' && b /= b')

            {-
                List of contexts that fit `selector`'s predicate.
            -}
            candidates = gsel selector graph


            {-
                Evaluate to true on any node with inward edges that do not have completely
                unique labels, as this means there's two or more substitutions being attempted
                on the same type variable.
            -}
            selector (inward, _, _, _) = any hasSome $ groupByEdgelabel inward

            {-
                Get the clash root paths for an individual context. These get
                concatinated to a list for all the contexts.
            -}
            findClashRootPaths :: Graph.Context t p -> [ClashTreeRoot t p]
            findClashRootPaths ctx = buildClashRootPaths <$> ctxGroups where
                {-
                    Contexts grouped by their edge labels towards ctx, all groups with <2 elements
                    have been filtered out due clashes being defined as there being two or more inward
                    edges with the same label.
                -}
                ctxGroups =
                    fmap (context graph . (^._2)) <$> filter hasSome (groupByEdgelabel (ctx^._1))

                {-
                    Build the clash root path for an individual group.
                -}
                buildClashRootPaths :: [Graph.Context t p] -> ClashTreeRoot t p
                buildClashRootPaths ctxs = (paths, lab' ctx) where
                    {-
                        The original context but with it's inward edges that aren't in
                        the provided group removed.
                    -}
                    ctx' :: Graph.Context t p
                    ctx' = ctx Lens.& _1 %~ filter ((`Set.member` ctxsNodeSet) . snd)

                    {-
                        Set of all nodes labels of the group.
                    -}
                    ctxsNodeSet = Set.fromList $ node' <$> ctxs

                    {-
                        All the paths leading to the final context.
                    -}
                    paths :: [Tree (t, [p])]
                    paths = fmap fst <$> (treeRootStatefulBy statef ctx' graph <$> ctxs) where
                        {-
                            Function that given a previous context and a current context,
                            builds a tuple of the current context's label and the labels of
                            all edges from the current context to the previous context.
                        -}
                        statef :: Graph.Context t p -> Graph.Context t p -> ((t, [p]), Graph.Context t p)
                        statef ctxPre ctxCurr = ((lab' ctxCurr, subbed), ctxCurr) where
                            -- The list of all type variables in the previous context substituted
                            -- by the label of the current context
                            subbed = fst <$> filter ((== node' ctxPre) . snd) (ctxCurr^._4)
