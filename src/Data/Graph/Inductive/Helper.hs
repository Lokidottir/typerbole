module Data.Graph.Inductive.Helper where

import           Data.Graph.Inductive as Graph
import qualified Data.List.Ordered    as Ord
import qualified Data.Map             as Map
import           Data.Maybe
import qualified Data.Set             as Set
import           Data.Tuple
import qualified Data.Tree            as Tree
import qualified Data.List.NonEmpty   as NE
import           Control.Lens hiding ((&))

findRootPaths :: Graph gr => gr n e -> Graph.Context n e -> (Node, [[Node]])
findRootPaths = findRootPathsBy (\(_, node, _, _) -> node)

findRootPathsBy :: Graph gr => (Graph.Context n e -> a) -> gr n e -> Graph.Context n e -> (a, [[a]])
findRootPathsBy f graph ctx = (f ctx, findRootPathsRec [] ctx) where
    findRootPathsRec path ctx'@(inward, _, _, _) = case inward of
        [] -> [f ctx' : path]
        a  -> concatMap (findRootPathsRec (f ctx' : path) . context graph . snd) a

treeRootStatefulBy
    :: Graph gr
    => (st -> Graph.Context n e -> (a, st)) -- ^ The stateful fold function
    -> st                                   -- ^ The initial state
    -> gr n e                               -- ^ The graph to traverse
    -> Graph.Context n e                    -- ^ The initial context
    -> Tree.Tree (a, st)                    -- ^ The resulting tree of values and states at each node.
treeRootStatefulBy f st graph = trsbRec st where
    trsbRec st' ctx'@(inward, _, _, _) =
        let val = f st' ctx'
        in Tree.Node val (trsbRec (snd val) . context graph . snd <$> inward)

cyclesOfGraph :: Graph gr => gr n l -> [[LNode n]]
cyclesOfGraph graph = fromMaybe []   -- give a default to bring this out of the Maybe
                    . sequence       -- sequence again from [Maybe [...]] to Maybe [[...]]
                    . fmap           -- construct lnodes from each bare node
                            ( sequence -- sequence from [Maybe ...] t0 Maybe [...]
                            . fmap (\n -> (,) n <$> lab graph n)) -- make the lnode from the node
                    . filter hasSome -- filter out any with only 1 element
                    . scc $ graph    -- get the strongly connected components

{-|
    Given a graph, generate a possibly empty list of subgraphs that are the it's cycles.
-}
cyclicSubgraphs :: forall gr n e. (DynGraph gr, Ord n, Ord e) => gr n e -> [gr n e]
cyclicSubgraphs graph = flip subgraph graph <$> filter hasSome (scc graph)

-- | Returns true if a list has more than 1 element
hasSome :: [a] -> Bool
hasSome []  = False
hasSome [_] = False
hasSome _   = True

-- | Returns true if a list of contexts has more than one element or a loop in it's only element.
hasSome' :: [Graph.Context n l] -> Bool
hasSome' [] = False
hasSome' [(_, noden, _, outward)] = any ((== noden) . snd) outward
hasSome' _ = True

{-|
    Build a graph with no edges from a foldable container of node values.
-}
buildFromNodes :: (DynGraph gr, Foldable t) => t a -> gr a ()
buildFromNodes =
    fst . foldr (\n (gr, h : tl) -> (([], h, n, []) & gr, tl)) (Graph.empty, [(0 :: Node)..])

{-|
    A version of topsort that returns cycles as groups rather than
    incorperating them into it's result arbitrarily.

    It's result is a list of eithers, with Left values representing
    cycles and Right values as nodes not within a cycle, in an order
    similar to what is given by a regular topsort.
-}
topsortWithCycles :: (Graph gr, Ord a) => gr a b -> [Either [a] a]
topsortWithCycles graph =
    let
        -- Map of all nodes that are within a cycle to the cycle they are a member of.
        -- Given the cycle finding function uses fgl's strongly connected components
        -- function, there should be no nodes that exist in more than one cycle.
        cycleMap = Map.fromList . concat $ (\cy -> zip cy (repeat (Set.fromList cy))) . fmap snd <$> cyclesOfGraph graph
        -- Get the initial topsort.
        tsorted  = topsort' graph
        -- Crummy hack to sieve out cycles as they appear in the topsort result
        sieveCycles []     = []
        sieveCycles (h : tl) = case Map.lookup h cycleMap of
            Nothing -> Right h : sieveCycles tl
            Just cy -> Left (Set.toList cy) : sieveCycles (filter (`Set.notMember` cy) tl)
    in sieveCycles tsorted

{-|
    Convert a tree into a list of all of it's paths.
-}
treeToPaths :: Tree.Tree a -> [[a]]
treeToPaths (Tree.Node l []) = [[l]]
treeToPaths (Tree.Node l sbf) = (l :) <$> concat (treeToPaths <$> sbf)

{-|
    Unlabel a graph but without losing as much information.

    This transforms the graph by merging individual edge labels with their origin
    nodes.

    A Node labelled X with outward edges with labels [a,b,c] would be converted to
    Nodes (X,a) (X,b) and (X,c). Each node would have the inward edges of the original
    node X, although with respect to the transform being applied to all.

    Nodes without any outward edges or loops will be lost by the process.
-}
unlabelOutward :: forall gr n e. (DynGraph gr, Ord n, Ord e) => gr n e -> gr (n, e) ()
unlabelOutward graph = run_ empty $ do
    let es = fmap unnode'' . Ord.nubSort . concatMap edgeTransform $ labEdges graph
    insMapNodesM ns
    insMapEdgesM es where
        -- all the old nodes, transformed to map to each of their edges.
        ns = Ord.nubSort $ concatMap ctxToNewNodes (gsel (const True) graph)

        {-|
            Transform an edge into a set of edges.

            The target (second node of the input 3-tuple) has outward edges, and for
            each of them a new node in the final graph will be created.
        -}
        edgeTransform :: (Node, Node, e) -> [((Node, e), (Node, e), ())]
        edgeTransform (origin, target, label) = (\n -> (origin', n, ())) <$> targetsNewNodes where
            targetsNewNodes = (,) target . fst <$> (context graph target)^._4

            -- Origin node with the edge label
            origin' = (origin, label)

        ctxToNewNodes :: Graph.Context n e -> [(n, e)]
        ctxToNewNodes (_, _, nl, outward) = (,) nl . fst <$> outward

        unnode :: Node -> n
        unnode = lab' . context graph

        unnode' :: (Node, e) -> (n, e)
        unnode' = _1 %~ unnode

        unnode'' :: ((Node, e), (Node, e), ()) -> ((n, e), (n, e), ())
        unnode'' = (_1 %~ unnode') . (_2 %~ unnode')

        unnode''' :: ((Node, e), (Node, e), ()) -> ((n, e), (n, e), ())
        unnode''' = (_1._1 %~ lab' . context graph) . ((_2._1 %~ lab' . context graph))
