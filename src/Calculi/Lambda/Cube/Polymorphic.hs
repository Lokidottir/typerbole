{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Calculi.Lambda.Cube.Polymorphic (
    -- * Typeclass for Polymorphic Typesystems
      Polymorphic(..)
    , Substitution(..)
    -- ** Notation and related functions
    , hasSubstitutions
    , (⊑)
    , (\<)
    , areEquivalent
    , (≣)
    , (\-/)
    , generalise
    , generalise'
    , applyAllSubs
    , applyAllSubsGr
    , unify
    , typeVariables
    , boundTypeVariables
    , typeConstants
    -- * Substitution Validation
    , ClashTreeRoot
    , SubsErr(..)
    -- ** Typechecking context
    , SubsContext(..)
    , SubsContext'
    -- *** SubsContext lenses
    , subsMade
    , tape
    -- ** Validation related functions
    , subsToGraph
    , subsToGraphGr
    , subsToGraphM
    , unvalidatedApplyAllSubs
    , topsortSubs
    , topsortSubsG
) where

import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Typechecking
import           Control.Monad
import           Control.Monad.State.Class
import           Data.Either.Combinators
import           Data.Bifunctor
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
    A TypingContext
-}
data SubsContext t p = SubsContext {
      _subsMade :: Map.Map p t
    -- ^ The substitutions made so far, where the key
    , _tape :: [p]
    -- ^ An infinite list of polytypes not present in the who typing context.
} deriving (Eq, Ord)
makeLenses ''SubsContext

{-|
    Datatype describing possible substitutions found by the `substitutions` Polymorphic
    typeclass method.
-}
data Substitution t p =
      Mutual p p
      -- ^ Two equivalent polytypes that could substitute eachother.
    | Substitution t p
      -- ^ A substitution of type expression @t@ over polytype @p@
    deriving (Eq, Ord, Show)

{-|
    Note: only shows the first 10 elements of the infinte list.
-}
instance (Show t, Show p) => Show (SubsContext t p) where
    show (SubsContext s tp) = "SubsContext (" ++ show s ++ ") (" ++ show (take 10 tp) ++ ")"

{-|
    `SubsContext` but assumes the poly type representation of @t@ is the second argument.
-}
type SubsContext' t = SubsContext t (PolyType t)

{-|
    Class of typesystems that exhibit polymorphism.
-}
class (Ord (PolyType t), SimpleType t) => Polymorphic t where

    {-|
        The representation of a poly type, also reffered to as a type variable.
    -}
    type PolyType t :: *

    {-|
        Find the substitutions between two type expressions. If there's
        a mismatch in structure then report the values passed as a Left
        value.

        ===Behaviour

        * A substitution of a poly type \"a\" for mono type \"X\"

            @`substitutions` (X) (a) = Right [`Substitution` (X) (a)]@

        * Two type expressions have substitutions between eachother.

            >>> substitutions (a → B) (X → b)
            Right [`Substitution` (X) (a), `Substitution` (B) (b)]@

        * A mutual substitution between two poly types.

            @`substitutions` (a) (b) = Right [`Mutual` (a) (b)]@

        * Mismatches in structure.

            @`substitutions` (X) (Y) = Left [(X, Y)]@

            @`substitutions` (C → x C) (x C) = Left [(C → x C, x C)]@

    -}
    substitutions :: t -> t -> Either [(t, t)] [Substitution t (PolyType t)]

    {-|
        Substitution application, given one type expression substituting a poly type and a
        target type expression, substitute all instances of the poly type in the target
        type expression with the type expression substituting it.

        ===Behaviour

        * Substituting all instance of \"a\" with \"X\"

            @`applySubstitution` X a (∀ a b. a → b → a) = (∀ b. X → b → X)@

        * Substitution application in a type expression with a type constructor.

            @`applySubstitution` (X → Y) x (M x) = (M (X → Y))@

        * Applying a substitution to a type expression that doesn't contain the poly type
          being substituted

            @`applySubstitution` Y x (M Q) = (M Q)@
    -}
    applySubstitution :: t -> PolyType t -> t -> t

    {-|
        Quantify instances of a poly type in a type expression.

        ===Behaviour

        * Quantifying a type variable that appears in a type expression.

            @`quantify` a (a → X) = (∀ a. a → X)@

        * Quantifying a type variable that doesn't appear in a type expression

            @`quantify` a (b → X) = (∀ a. b → X)@
    -}
    quantify :: PolyType t -> t -> t

    {-|
        Split a quantification into it's variable being quantified and
        the expression targeted by the quantification. A safe inverse of `quantify`.

        ===Behaviour

        * Unquantifying a type expression that quantifies a single poly type.

            @`unquantify` (∀ a. a → b) = Just (a, a → b)@

        * Unquantifying a type expression that quantifies multiple poly types

            @`unquantify` (∀ a b. a b) = Just (a, ∀ b. a b)@

        * Unquantifying a type expression that quantifies none of it's poly types.

            @`unquantify` (A b) = Nothing@
    -}
    unquantify :: t -> Maybe (PolyType t, t)

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Poly p".
    -}
    poly :: PolyType t -> t

    {-|
        Function retrives all the free type variables in a type.
        If the type is itself an unbound poly type, then that is returned.

        ===Behaviour

        * Type expression with some of it's poly types quantified.

            @`freeTypeVariables` (∀ a b. a → b → c d)) = `Set.fromList` [c, d]@

        * Type expression with no quantified poly types.

            @`freeTypeVariables` (a → b → c) = `Set.fromList` [a, b, c]@

        * Type expression with no unquantified poly types.

            @`freeTypeVariables` (∀ c. X → c) = `Set.empty`@
    -}
    freeTypeVariables :: t -> Set.Set t

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
(⊑) :: Polymorphic t => t -> t -> Bool
t ⊑ t' =
    let
        convertMutual (Mutual b a) = (poly a,  b)
        convertMutual (Substitution a b) = (a,  b)

        {-
            Get all the substitutions of t' over t, and map the substitution mismatches
            with the SubsMismatch error constructor.
        -}
        subs = fmap (uncurry SubsMismatch) `first` substitutions t' t
        {-
            Assuming getting the substitutions succeeded, validate and apply them together.
        -}
        appedSubs = fmap convertMutual <$> subs >>= applyAllSubsGr
        {-
            Assuming the substitutions were valid, pull the substitution function out of
            Either, using the identity function in case of a Left value.
        -}
        appedSubs' = fromRight id appedSubs
        -- Assuming the substitutions succeeded and were valid, check that t' is equal to the
        -- substitutions it implies for t being applied to t.
    in isRight appedSubs && t' ≣ appedSubs' t

infix 4 ⊑

{-|
    Non-unicode @(⊑)@.
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
typeVariables t = Set.fromList . concatMap (\(Mutual a b) -> poly <$> [a, b]) $ fromRight [] (substitutions t t)

{-|
    Bound type variables of an expression.
-}
boundTypeVariables :: Polymorphic t => t -> Set.Set t
boundTypeVariables t = Set.difference (typeVariables t) (freeTypeVariables t)

{-|
    Type constants/Mono types of a type expression.
-}
typeConstants :: Polymorphic t => t -> Set.Set t
typeConstants t = Set.difference (bases t) (typeVariables t)

{-|
    Quantify every free type variable in a type expression, excluding a
    set of free type variables to not quantify.

    @`generalise` `Set.empty` (x → y) = (∀ x y. x → y)@

    @`generalise` (`Set.fromList` [a, b]) (a → b → c) = (∀ c. a → b → c) @
-}
generalise :: forall t. Polymorphic t => Set.Set t -> t -> t
generalise exclude t = foldr quantify t ftvsBare where
    ftvsBare :: Set.Set (PolyType t)
    ftvsBare = Set.fromList $ snd <$> filter (flip Set.member ftvs . fst) polyTypes where
        ftvs = Set.difference (freeTypeVariables t) exclude
        polyTypes :: [(t, PolyType t)]
        polyTypes = fmap (\(Mutual a b) -> (poly a, b)) . fromRight [] $ substitutions t t

{-|
    `generalise` but with an empty exclusion set.
-}
generalise' :: Polymorphic t => t -> t
generalise' = generalise Set.empty

{-|
    Unify two type expressions.
-}
unify :: forall gr t p. (Polymorphic t, DynGraph gr, PolyType t ~ p)
      => [p]          -- ^ An infinite list of type variables that don't exist in either type expressions
                      -- or a greater typing context.
      -> t            -- ^ The first type expression.
      -> t            -- ^ The second type expression.
      -> Either [SubsErr gr t p] (Unification t p)
                      -- ^ The result, either substitution errors or a tuple of the remaining
                      -- poly types in the infinte list and the
unify tape t1 t2 = do
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
    A type alias triple, where the first element is the remaining infinite
    list of type variables, the second is the ones that were consumed
-}
type Unification t p = ([p], [(t, p)])

{-|
    Calculate if one type can substitute another, should check if there are any error in the
    substitutions such as cycles or multiple possible substitutions, then return true if
    either both are identical or the substitutions don't conflict.
-}
hasSubstitutions :: forall t. Polymorphic t => t -> t -> Bool
hasSubstitutions x y = isRight (applyAllSubsGr =<< processSubs (substitutions x y)) where
    processSubs = bimap (uncurry SubsMismatch <$>) (catMaybes . fmap convertMutual) where
        convertMutual (Substitution t1 t2) = Just (t1, t2)
        convertMutual (Mutual t1 t2) = Just (poly t1, t2)


{-|
    Check if two types are equivalent, where equivalence is defined as the substitutions
    being made being symbolically identical, where binds and type variables appear in
    the same place but may have different names (this is Alpha Equivalence).

    @`areEquivalent` (∀ a. X → a) (∀ z. X → z) = True@

    @`areEquivalent` (M → X) (M → X) = True@

    @`areEquivalent` (∀ a. a) (∀ z. z → z) = False@
-}
areEquivalent :: forall t. Polymorphic t => t -> t -> Bool
areEquivalent x y = fromRight False $ all isMutual <$> subs where
    subs = substitutions x y

    isMutual (Mutual _ _) = True
    isMutual _            = False

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
