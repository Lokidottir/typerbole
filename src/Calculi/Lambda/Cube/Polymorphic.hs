{-# LANGUAGE FlexibleContexts #-}
module Calculi.Lambda.Cube.Polymorphic (
      -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
    , Substitution
      -- ** Notation and related functions
    , canSubstitute
    , (⊑)
    , (\<)
    , areEquivalent
    , (≣)
    , (\-/)
    , generalise
    , generalise'
    , applyAllSubs
    , typeVariables
    , boundTypeVariables
      -- * Substitution Validation
    , SubsErr(..)
    , ClashTreeRoot
      -- ** Validation related functions
    , subsToGraph
    , subsToGraphGr
    , subsToGraphM
    , unvalidatedApplyAllSubs
    , topsortSubs
    , topsortSubsG
) where

import           Calculi.Lambda.Cube.SimpleType
import           Control.Monad
import           Control.Monad.State.Class
import           Data.Either.Combinators
import           Data.Function hiding ((&))
import           Data.Graph.Inductive as Graph
import           Data.Graph.Inductive.Helper
import           Data.List.Ordered
import           Data.List (groupBy)
import qualified Data.Map                       as Map
import           Data.Maybe
import qualified Data.Set                       as Set
import           Data.Tuple
import           Debug.Trace
import           Data.Tree
import           Control.Lens as Lens hiding ((&))
import qualified Control.Lens as Lens ((&))

{-|
    A type alias for substitutions, which are just endomorphisms.
-}
type Substitution t = t -> t

{-|
    A substitution clash's root, with a tree of types substituting
    variables as the first element [1] and the second element being the
    type where these clashing substitutions converge.

    [1]: to be read that the first element of the tuple is a forest of
    substitutions leading the final type (the second element), and
    because of their convergence the first layer of the trees should
    all be substituting the same variable.
-}
type ClashTreeRoot t p = ([Tree (t, [p])], t)

-- TODO: Maybe rename the constructors and recomment
data SubsErr gr t p =
      MultipleSubstitutions (ClashTreeRoot t p)
    -- ^ There are multiple possible substitutions, the first argument here
    -- is the type that has multiple substitutions and the second is the
    -- list of all the conflicting substitutions' paths.
    | CyclicSubstitution (gr t p)
    -- ^ There is a cycle of
    deriving (Eq, Show, Read)

{-|
    Class of typesystems that exhibit polymorphism.
-}
class (Ord (PolyType t), SimpleType t) => Polymorphic t where

    {-|
        The representation of a poly type, also reffered to as a type variable.
    -}
    type PolyType t :: *

    {-|
        Generates a list of tuples representing the possible substitutions that
        can be made when the first type is substituting the second.

        Doesn't have to be checked within this function, as subsToGraph performs
        a significant amount of analysis that is used in `canSubstitute`'s default
        implementation.

        @`substitutions` (T → G) (∀ a. (∀ b. a → b)) = Just [(T, a), (G, b)]@

        @`substitutions` (∀ a. a -> a) (∀ b. b) = Just [(a -> a, b)]@
    -}
    substitutions :: t -> t -> Maybe [(t, PolyType t)]

    {-|
        Substitution application, given one type substituting a type variable,
        generate a function that will apply the substitution in a type expression.

        @`applySubstitution` X a (∀ a b. a → b → a) = (∀ b. X → b → X)@

        @`applySubstitution` Y x (M x) = (M Y)@

        @`applySubstitution` Y x (M Q) = (M Q)@
    -}
    applySubstitution :: t -> PolyType t -> Substitution t

    {-|
        Quantify instances of a type variable in a type expression.

        @`quantify` a (a → X) = (∀ a. a → X)@
    -}
    quantify :: PolyType t -> t -> t

    {-|
        Split a quantification into it's variable being quantified and
        the expression targeted by the quantification. A safe inverse of `quantify`.
&&-}
    unquantify :: t -> Maybe (PolyType t, t)

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Poly p".
    -}
    poly :: PolyType t -> t

    {-|
        Function retrives all the free type variables in a type.
        If the type is itself an unbound poly type, then that is returned.

        @`freeTypeVariables` (∀ a. (∀ b. a → b → c d)) = `Set.fromList` [c, d]@

        @`freeTypeVariables` (a → b → c) = `Set.fromList` [a, b, c]@

        @`freeTypeVariables` (∀ c. X → c) = `Set.empty`@
    -}
    freeTypeVariables :: t -> Set.Set t

{-|
    Type ordering operator, true if the first argument is more specific or equal to
    the second.
-}
(⊑) :: Polymorphic t => t -> t -> Bool
t' ⊑ t =
    let
        {-
            Get all the substitutions of t' over t
        -}
        subs = substitutions t' t
        {-
            Assuming getting the substitutions succeeded, validate and apply them together.
        -}
        appedSubs = applyAllSubsGr (fromMaybe [] subs)
        {-
            Assuming the substitutions were valid, pull the substitution function out of
            Either, using the identity function in case of a Left value.
        -}
        appedSubs' = fromRight id appedSubs
        -- Assuming the substitutions succeeded and were valid, check that t' is equal to the
        -- substitutions it implies for t being applied to t.
    in isJust subs && isRight appedSubs && t' ≣ appedSubs' t

infix 4 ⊑

{-|
    Non-unicode `(⊑)`.
-}
(\<) :: Polymorphic t => t -> t -> Bool
(\<) = (⊑)

infix 4 \<

{-|
    Infix `areEquivalent`
-}
(≣) :: Polymorphic t => t -> t -> Bool
(≣) = areEquivalent

infix 4 ≣

{-|
    Infix `quantify`, looks a bit like @∀@ but doesn't interfere with unicode syntax extensions.
-}
(\-/) :: Polymorphic t => PolyType t -> t -> t
(\-/) = quantify

infixr 6 \-/

{-|
    All the type variables in a type expression, bound or unbound.
-}
typeVariables :: Polymorphic t => t -> Set.Set t
typeVariables t = Set.fromList $ poly . snd <$> fromMaybe [] (substitutions t t)

{-|
    Bound type variables of an expression.
-}
boundTypeVariables :: Polymorphic t => t -> Set.Set t
boundTypeVariables t = Set.difference (typeVariables t) (freeTypeVariables t)

{-|
    Quantify every free type variable in a type expression, excluding a
    set of free type variables to not quantify.

    @`generalise` Set.empty (x → y) = (∀ x y. x → y) @

    @`generalise` (Set.fromList []) @
-}
generalise :: forall t. Polymorphic t => Set.Set t -> t -> t
generalise exclude t = foldr quantify t ftvsBare where
    ftvsBare :: Set.Set (PolyType t)
    ftvsBare = Set.fromList $ snd <$> filter (flip Set.member ftvs . fst) polyTypes where
        ftvs = Set.difference (freeTypeVariables t) exclude
        polyTypes :: [(t, PolyType t)]
        polyTypes = fromMaybe [] $ substitutions t t

{-|
    `generalise` but with an empty exclusion set.
-}
generalise' :: Polymorphic t => t -> t
generalise' = generalise Set.empty

{-|
    Calculate if one type can substitute another, should check if there are any error in the
    substitutions such as cycles or multiple possible substitutions, then return true if
    either both are identical or the substitutions don't conflict.
-}
canSubstitute :: forall t. Polymorphic t => t -> t -> Bool
canSubstitute x y =
    -- NOTE: This doesn't work as implied by it's name on @canSubstitute (a → K) (M → b)@
    -- but it this is still valid as far as type theory (and ghci) is concerned
    fromMaybe False (isRight . subsToGraph' <$> substitutions x y) || x == y where
        subsToGraph' :: [(t, PolyType t)] -> Either [SubsErr Gr t (PolyType t)] (Gr t (PolyType t))
        subsToGraph' = subsToGraph

{-|
    Check if two types are equivalent, where equivalence is defined as the substitutions
    being made being symbolically identical, where binds and type variables appear in
    the same place but may have different names.

    @`areEquivalent` (∀ a. X → a) (∀ z. X → z) = True@

    @`areEquivalent` (M → X) (M → X) = True@

    @`areEquivalent` (∀ a. a) (∀ z. z → z) = False@
-}
areEquivalent :: forall t. Polymorphic t => t -> t -> Bool
areEquivalent x y = fromMaybe (x == y) $ do
    subs1 <- nubSort . mapPoly <$> substitutions x y -- get the sorted substitutions of the first
    subs2 <- nubSort . fmap swap . mapPoly <$> substitutions y x -- get the sorted substitutions of the second
    return (subs1 == subs2) where
        mapPoly = fmap (_2 %~ (poly :: PolyType t -> t))

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
topsortSubs = fmap topsortSubsG . (subsToGraph :: [(t, p)] -> Either [SubsErr gr t p] (gr t p))

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
unvalidatedApplyAllSubs :: (Polymorphic t, p ~ PolyType t) => [(t, p)] -> Substitution t
unvalidatedApplyAllSubs = foldr (\sub f -> uncurry applySubstitution sub . f) id

{-|
    Validate substitutions and fold them into a single substitution function.
-}
applyAllSubs :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr) => [(t, p)] -> Either [SubsErr gr t p] (Substitution t)
applyAllSubs = fmap unvalidatedApplyAllSubs . topsortSubs

applyAllSubsGr :: (Polymorphic t, p ~ PolyType t) => [(t, p)] -> Either [SubsErr Gr t p] (Substitution t)
applyAllSubsGr = applyAllSubs

{-|
    Function that builds a graph representing valid substitutions or reports
    any part of the graph's structure that would make the substitutions invalid.
-}
subsToGraph
    :: forall gr t p. (Polymorphic t, p ~ PolyType t, DynGraph gr)
    => [(t, p)]
    -> Either [SubsErr gr t p] (gr t p)
subsToGraph subs =
    let (errs, (_, graph :: gr t p)) = run empty (subsToGraphM subs)
    in if null errs then Right graph else Left errs

subsToGraphGr :: forall t p. (Polymorphic t, p ~ PolyType t)
              => [(t,p)]
              -> Either [SubsErr Gr t p] (Gr t p)
subsToGraphGr = subsToGraph
{-|
    A version of `subsToGraph` that works within fgl's NodeMap state monad.
-}
subsToGraphM
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
subsToGraphM subs = do
    {-
        Construct the graph so we have something to work with.
    -}
    -- Assemble a list of all the type expressions, including the substitution targets
    {- Note: to make this work from a point of theory, all the targets in "subs" are turned into
       type expressions using the polymorphic constructor, allowing all substitutions to
       have at least one edge from the substitutions to the targets. -}
    let typeExprs = nubSort $ concat ((\(t, p) -> [t, poly p]) <$> subs)
    -- Build a list of type expressions and their bases.
    let basesList = (\t -> (t, typeVariables t)) <$> typeExprs
    -- Construct the edges
    let subsEdges = buildEdge <$> subs <*> basesList
    -- Insert the nodes. (crashes if this isn't done first, because fgl!)
    void (insMapNodesM typeExprs)
    -- Insert the edges.
    insMapEdgesM (catMaybes subsEdges)
    -- Compute and return the errors
    validateAsSubsgraph <$> gets snd where
        {-
            Given a substitution pair and pair of a type expression and it's
            base types, check if the substitution's own target appears in those
            base types.
        -}
        buildEdge :: (t, p) -> (t, Set.Set t) -> Maybe (t, t, p)
        buildEdge (t1, p) (t2, t2'bases)
            | poly p `Set.member` t2'bases = Just (t1, t2, p)
            | otherwise = Nothing

        {-
            Generate a possibly empty list of substitution errors in the graph that was
            built.
        -}
        validateAsSubsgraph :: gr t p -> [SubsErr gr t p]
        validateAsSubsgraph graph =
            let cycles = cyclicSubgraphs graph
                clashes = clashesOfGraph graph
            in if not (null cycles) then
                -- If ther are cycles, return them after passing them through the error constructor.
                CyclicSubstitution <$> cycles
                else if not (null clashes) then
                    MultipleSubstitutions <$> clashes
                    else []

        {-|
            Generate a list of trees of fully labelled edges,
        -}
        clashesOfGraph :: gr t p -> [ClashTreeRoot t p]
        clashesOfGraph graph = concatMap findClashRootPaths candidates where

            {-|
                List of contexts that fit `selector`'s predicate.
            -}
            candidates = gsel selector graph

            {-|
                Evaluate to true on any node with inward edges that do not have completely
                unique labels, as this means there's two or more substitutions being attempted
                on the same type variable.
            -}
            selector (inward, _, _, _) = any hasSome $ groupByEdgelabel inward

            {-|
                Get the clash root paths for an individual context. These get
                concatinated to a list for all the contexts.
            -}
            findClashRootPaths :: Graph.Context t p -> [ClashTreeRoot t p]
            findClashRootPaths ctx = buildClashRootPaths <$> ctxGroups where
                {-|
                    Contexts grouped by their edge labels towards ctx, all groups with <2 elements
                    have been filtered out due clashes being defined as there being two or more inward
                    edges with the same label.
                -}
                ctxGroups =
                    fmap (context graph . (^._2)) <$> filter hasSome (groupByEdgelabel (ctx^._1))

                {-|
                    Build the clash root path for an individual group.
                -}
                buildClashRootPaths :: [Graph.Context t p] -> ClashTreeRoot t p
                buildClashRootPaths ctxs = (paths, lab' ctx) where
                    {-|
                        The original context but with it's inward edges that aren't in
                        the provided group removed.
                    -}
                    ctx' :: Graph.Context t p
                    ctx' = ctx Lens.& _1 %~ filter ((`Set.member` ctxsNodeSet) . snd)

                    {-|
                        Set of all nodes labels of the group.
                    -}
                    ctxsNodeSet = Set.fromList $ node' <$> ctxs

                    {-|
                        All the paths leading to the final context.
                    -}
                    paths :: [Tree (t, [p])]
                    paths = fmap fst <$> (treeRootStatefulBy statef ctx' graph <$> ctxs) where
                        {-|
                            Function that given a previous context and a current context,
                            builds a tuple of the current context's label and the labels of
                            all edges from the current context to the previous context.
                        -}
                        statef :: Graph.Context t p -> Graph.Context t p -> ((t, [p]), Graph.Context t p)
                        statef ctxPre ctxCurr = ((lab' ctxCurr, subbed), ctxCurr) where
                            -- The list of all type variables in the previous context substituted
                            -- by the label of the current context
                            subbed = fst <$> filter ((== node' ctxPre) . snd) (ctxCurr^._4)

        {-|
            Group by equality on the first element (edge label) and inequality on the second.
        -}
        groupByEdgelabel :: (Eq a, Eq b) => [(a, b)] -> [[(a, b)]]
        groupByEdgelabel = groupBy (\(a, b) (a', b') -> a == a' && b /= b')
