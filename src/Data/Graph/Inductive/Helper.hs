module Data.Graph.Inductive.Helper where

import           Data.Graph.Inductive as Graph
import qualified Data.List.Ordered    as Ord
import qualified Data.Map             as Map
import           Data.Maybe
import qualified Data.Set             as Set
import           Data.Tuple
import qualified Data.Tree            as Tree

{-|
    Given a list of pairs of an orderable type, will build a graph representing
    the nodes and their edges, and a map to get the the fgl node representation
    of an element for any present node label.
-}
edgesToGraph :: (Ord a, Graph gr) => [(a, a)] -> (gr a (), Map.Map a Node)
edgesToGraph es = (mkGraph (swap <$> labeledNodes) (lookupEdge <$> es), nodeMap) where
    -- Function looking up node label pairs to node numbers.
    lookupEdge e = let luEdge = fromJust . (`Map.lookup` nodeMap)
                   in (luEdge (fst e), luEdge (snd e), ())
    -- Map of node labels to node numbers
    nodeMap = Map.fromList labeledNodes
    -- ordered list of labeled nodes and node numbers
    labeledNodes = flip zip [0 :: Node, 1..]
                 . Ord.nub
                 . Ord.sort
                 . concatMap (\(a,b) -> [a,b]) $ es

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

cyclesOfGraphMay :: (Graph gr, Ord n, Ord e) => gr n e -> Maybe [[(n, n, e)]]
cyclesOfGraphMay graph = do
    -- Get a list of all cycles, replacing the node number with the node's context.
    let cyclesInitial = fmap (\(_,nn,_,_) -> nn) <$> filter hasSome' (fmap (context graph) <$> scc graph)
    let cycles = undefined
    undefined

-- | Returns true if a list has more than 1 element
hasSome :: [a] -> Bool
hasSome []  = False
hasSome [_] = False
hasSome _   = True

-- | Returns true if a list of contexts has more than one element or a loop in it's only element.
hasSome' :: [Context n l] -> Bool
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
