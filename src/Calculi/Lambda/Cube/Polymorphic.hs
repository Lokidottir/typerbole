{-# LANGUAGE ScopedTypeVariables #-}
module Calculi.Lambda.Cube.Polymorphic where

import           Calculi.Lambda.Cube.SimpleType
import           Control.Monad
import           Control.Monad.State.Class
import           Data.Either
import           Data.Function hiding ((&))
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Helper
import           Data.List.Ordered
import           Data.List (groupBy)
import qualified Data.Map                       as Map
import           Data.Maybe
import qualified Data.Set                       as Set
import           Data.Tuple
import           Debug.Trace
import           Data.Tree

{-|
    A type alias for substitutions, which are just endomorphisms.
-}
type Substitution t = t -> t

-- TODO: Maybe rename the constructors and recomment
data SubsErr t =
      MultipleSubstitutions t [[t]]
    -- ^ There are multiple possible substitutions, the first argument here
    -- is the type that has multiple substitutions and the second is the
    -- list of all the conflicting substitutions' paths.
    | CyclicSubstitution [t]
    -- ^ There's a cycle in the substitutions.
    | BranchConverge t [[t]]
    -- ^ There exists a node with multiple substitutions that originate from
    -- the same root. The first node is that node with multiple substitutions,
    -- while the second is a list of paths from the root.
    deriving (Eq, Ord, Show, Read)

data InferenceEnvironment v t = InferenceEnvironment

{-|
    Class of typesystems that exhibit polymorphism.
-}
class (SimpleType t) => Polymorphic t where

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
    substitutions :: t -> t -> Maybe [(t, t)] -- TODO: do the work to let this be Maybe [(t, PolyType t)]

    {-|
        Substitution application, given one type substituting another, generate a function
        that will apply this substitution to a given type.
    -}
    applySubstitution :: t -> t -> Substitution t

    {-|
        Quantify instances of a type variable in a type expression.

        @`quantify` a (a → X) = (∀ a. a → X)@
    -}
    quantify :: PolyType t -> t -> t

    {-|
        Split a quantification into it's variable being quantified and
        the expression targeted by the quantification. A safe inverse of `quantify`.

        @`unquantify` (∀ a. M → a) = Just (a, M → a)@

        @`unquantify` (X → b) = Nothing@
    -}
    unquantify :: t -> Maybe (PolyType t, t)

    {-|
        Calculate if one type can substitute another, should check if there are any error in the
        substitutions such as cycles or multiple possible substitutions, then return true if
        either both are identical or the substitutions don't conflict.

        This is a lot to ask for, thankfully this is already implemented in terms of
        `substitutions` and `subsToGraph`, this is here in case there's a more efficient
        algorithm the library user knows about.
    -}
    canSubstitute :: t -> t -> Bool
    canSubstitute x y =
        -- NOTE: This doesn't work as implied by it's name on @canSubstitute (a → K) (M → b)@
        -- but it this is still valid as far as type theory (and ghci) is concerned
        fromMaybe False (isRight . subsToGraph <$> substitutions x y) || x == y

    {-|
        Check if two types are equivalent, where equivalence is defined as the substitutions
        being made being symbolically identical, where binds and type variables appear in
        the same place but may have different names.

        @`areEquivalent` (∀ a. X → a) (∀ z. X → z) = True@

        @`areEquivalent` (M → X) (M → X) = True@

        @`areEquivalent` (∀ a. a) (∀ z. z → z) = False@
    -}
    areEquivalent :: t -> t -> Bool
    areEquivalent x y = fromMaybe (x == y) $ do
        subs1 <- nubSort <$> substitutions x y -- get the sorted substitutions of the first
        subs2 <- nubSort <$> substitutions y x -- get the sorted substitutions of the second
        return (subs1 == fmap swap subs2) -- swap the second's elements and check if equal

    {-|
        Polymorphic constructor synonym, as many implementations will have a constructor along
        the lines of "Poly p".
    -}
    poly :: PolyType t -> t

{-|
    Infix, flipped `canSubstitute` corresponding to the type ordering operator used in
    much of type theory.
-}
(⊑) :: Polymorphic t => t -> t -> Bool
(⊑) = flip canSubstitute

infix 4 ⊑

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
    Given a list of substitutions, i.e. the output of `substitutions`, generate a graph
    if there are no cycles or clashes, otherwise return the errors relating to those.

    TODO: define clashes outside of the internal comments for this function.
    TODO: use fgl's nodemap functionality instead of the hacks that were used here.
    TODO: check if we should have types as nodes and substitutions as edges instead
    NOTE: This currently is non-terminating under some unknown circumstances
-}
subsToGraph :: forall t. (SimpleType t) => [(t, t)] -> Either [SubsErr (t, t)] (Gr (t, t) ())
subsToGraph subsPairs
    -- if there are any cycles, return the errors relating to those before they cause problems
    -- in the other checks.
    | not . null $ cycles  = Left $ CyclicSubstitution . fmap snd <$> cycles
    -- if there are any clashes (see the clash comments for definition) then return errors
    -- relating to those.
    | not . null $ clashes = Left clashes
    -- otherwise we return the validated graph.
    | otherwise            = Right subsGraph
        where
            -- Generate the graph from edges and add any nodes that don't have any edges that
            -- were missed out.
            (subsGraph, _, _) =
                foldl accu (subsGraph', subsNodeMap, nodeList) subsPairs where
                    accu st@(_, _, []) _      = st
                    accu st@(gr, nm, h : tl) sub
                        | sub `Map.member` nm = st
                        | otherwise           = (([], h, sub, []) & gr, Map.insert sub h nm, tl)

                    {-
                        Infinite list of node numbers that do not appear in the generated graph,
                        so that we have a valid node number for any elements of subsPairs that
                        do not appear in the graph.
                    -}
                    nodeList :: [Node]
                    nodeList =
                        -- check if the map is empty because maximum isn't total
                        -- if it's empty then we return [0..]
                        if subsNodeMap == Map.empty then
                            [0..]
                            else
                                [succ $ maximum subsNodeMap ..]

                    (subsGraph' :: Gr (t, t) (), subsNodeMap) = edgesToGraph connections

            cycles = cyclesOfGraph subsGraph

            -- This is a pretty intense computation and definitely needs optimising,
            -- especially in 'hasConnection', where the results of 'bases' could be
            -- memoized.
            connections = catMaybes (genEdge <$> subsPairs <*> subsPairs) where
                {-
                    Generate an edge if the first tuple's second element appears in the
                    second tuple's first element.
                -}
                genEdge :: (t, t) -> (t, t) -> Maybe ((t, t), (t, t))
                genEdge a b
                    | hasConnection a b = Just (a, b)
                    | otherwise         = Nothing where
                        hasConnection :: (t, t) -> (t, t) -> Bool
                        hasConnection (_, target) (sub, _) = target `Set.member` bases sub

            -- clashes are occurences of a substitution with more than one inward edge
            clashes = catMaybes (errorsOf <$> clashCandidates) where
                -- All the nodes with more than one inward edge are a clash, but
                -- the kind of clash is yet to be determined.
                clashCandidates = gsel (\(inward, _, _, _) -> hasSome inward) subsGraph
                -- given a context, generate any errors that may appear.
                errorsOf = pathsToError . findRootPathsBy lab' subsGraph
                {-
                    Given a tuple of a node and a list of the paths from it's roots
                    to itself, determine if there is an error
                -}
                pathsToError pair@(_, paths)
                    | not (hasSome paths) = Nothing
                    | Set.size roots == 1      = Just (uncurry BranchConverge pair)
                    | otherwise                = Just (uncurry MultipleSubstitutions pair) where
                        roots = rootsFromPaths paths where
                            {-
                                Determine the set of roots a list of paths has, assuming the root is always
                                the first element of a path.
                            -}
                            rootsFromPaths :: Ord a => [[a]] -> Set.Set a
                            rootsFromPaths = foldl (\st path -> Set.insert (head path) st) Set.empty

data SubsErr' t p =
      CyclicSubstitution' [(t, t, p)]
    | MultipleSubstitutions' p [[(t, t, p)]]

subsToGraph'
    :: forall t p gr. (Polymorphic t, p ~ PolyType t, Ord p, DynGraph gr)
    => [(t, p)]
    -> Either [SubsErr' t p] (gr t p)
subsToGraph' subs =
    let (errs, (_, graph :: gr t p)) = run empty (subsToGraphM subs)
    in if null errs then Right graph else Left errs

{-|
    A version of `subsToGraph` that works within fgl's NodeMap state monad.
-}
subsToGraphM
    :: forall t p gr. -- No haddock documentation for constraints, so documentation is in source
    ( Polymorphic t   -- The typesystem @t@ is a an instance of Polymorphic
    , p ~ PolyType t  -- @p@ is @t@'s representation of type variables
    , Ord p           -- t's representation of type variables is ordered
    , DynGraph gr     -- the graph representation is an instance of DynGraph
    )
    => [(t, p)]       -- ^ A list of substitutions
    -> NodeMapM t p gr [SubsErr' t p]
                      -- ^ A nodemap monadic action where the graph's edges are substitutions
                      -- and the nodes are types where substitutions should be
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
    let basesList = (\t -> (t, bases t)) <$> typeExprs
    -- Construct the edges
    let subsEdges = buildEdge <$> subs <*> basesList
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

        validateAsSubsgraph :: gr t p -> [SubsErr' t p]
        validateAsSubsgraph graph =
            let cycles = fromMaybe [] (cyclesOfGraphMay graph)
                clashes :: [(p, [[(t, t, p)]])]
                clashes = undefined
            in if not (null cycles) then
                -- If ther are cycles, return them after passing them through the error constructor.
                CyclicSubstitution' <$> cycles
                else if not (null clashes) then
                    uncurry MultipleSubstitutions' <$> clashes
                    else []

        clashesOfGraph :: gr t p -> [(p, Node, [(t, t, p)])]
        clashesOfGraph graph = undefined where

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
                Group by equality on the first element (edge label).
            -}
            groupByEdgelabel :: Eq a => [(a, b)] -> [[(a, b)]]
            groupByEdgelabel = groupBy (on (==) fst)

        {-|
            DFS algorithm for finding the paths of substitution clashes.
        -}
        clashPaths :: gr t p -> [Node] -> Tree (LEdge p)
        clashPaths graph nodes = undefined
