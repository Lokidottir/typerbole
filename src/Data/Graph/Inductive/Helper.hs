module Data.Graph.Inductive.Helper where

import           Control.Monad.State
import           Data.Bifunctor
import           Data.Graph.Inductive as Graph
import qualified Data.Map             as Map
import           Data.Maybe
import           Data.Semigroup
import qualified Data.Set             as Set
import qualified Data.Tree            as Tree
import           Safe

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
cyclicSubgraphs graph = flip subgraph graph <$> filter hasSomeLI (scc graph) where
    -- hasSome but is inclusive of loops (nodes with edges to itself)
    hasSomeLI :: [Node] -> Bool
    hasSomeLI [] = False
    hasSomeLI [n] = not . null $ filter (\(n1,n2,_) -> n == n1 && n1 == n2) (out graph n ++ inn graph n)
    hasSomeLI _ = True

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
    Build a topsort inclusive of outward edges. Nodes without outward edges
    are ignored.

    If there are cycles in the graph, Nothing is returned.
-}
edgeyTopsort :: Graph gr => gr n e -> Maybe [(n, e)]
edgeyTopsort graph
    | not (null (cyclesOfGraph graph)) = Nothing
    | otherwise = Just (unvalidatedEdgeyTopsort graph)

{-|
    `edgeyTopsort` but doesn't check for cycles first.
-}
unvalidatedEdgeyTopsort :: Graph gr => gr n e -> [(n, e)]
unvalidatedEdgeyTopsort graph =
    {-
        In a cycle-less graph, there should always be 1 node
        that has no inward edge. If there's not, then we've
        finished the topsort
    -}
    let candidate = headMay $ gsel (null . inn') graph
    in case flip match graph . node' <$> candidate of
        Nothing                 -> []
        Just (Nothing, _)       -> []
        Just (Just ctx, graph') -> fmap (\(_, _, l) -> (lab' ctx, l)) (out' ctx) ++ unvalidatedEdgeyTopsort graph'

{-|
    Update the value for a node while retaining it's inward and outward edges,
    because this isn't an existing FGL thing apparantly.
-}
updateNode :: forall gr n e. (DynGraph gr) => Node -> (n -> n) -> gr n e -> gr n e
updateNode n f gr = flip execState gr $ do
    n'valMaybe <- gets lab <*> pure n
    -- Apply the update function to the node's value if it's there
    case f <$> n'valMaybe of
        -- If the node doesn't exist, then just return the graph as is
        Nothing -> return ()
        -- If the node does exist, update it's value
        Just n'val -> do
            -- get the inward and outward edges of the node
            n'edges <- mappend <$> (gets inn <*> pure n) <*> (gets out <*> pure n)
            -- delete them, and the node
            modify (delEdges (toEdge <$> n'edges))
            modify (delNode n)
            -- add the node back with it's new value
            modify (insNode (n, n'val))
            -- and add it's edges back.
            modify (insEdges n'edges)
            -- My kingdom for better graph library.

{-|
    Merge the values and edges of two given nodes.
-}
mergeNodes :: (Semigroup n, DynGraph gr) => Node -> Node -> gr n e -> Maybe (gr n e)
mergeNodes n1 n2 gr = mergeNodesBody <$> lab gr n1 where
    mergeNodesBody n1'val = flip execState gr $ do
        -- Get the (labeled) edges of n1
        n1'edges <- mappend <$> (gets inn <*> pure n1) <*> (gets out <*> pure n1)
        -- delete all the edges of n1
        modify (delEdges (toEdge <$> n1'edges))
        -- then delete n1
        modify (delNode n1)
        -- then merge the n1's value with n2's value
        modify (updateNode n2 (<> n1'val))
        -- then recreate all the edges of n1 but targeting or originating fron n2
        modify (insEdges $ replaceNodeInLEdgeWith n1 n2 <$> n1'edges)

mapNodeInEdge :: (Node -> Node) -> Edge -> Edge
mapNodeInEdge f = bimap f f

mapNodeInLEdge :: (Node -> Node) -> LEdge e -> LEdge e
mapNodeInLEdge f (a, b, el) = (f a, f b, el)

replaceNodeInEdgeWith :: Node -> Node -> Edge -> Edge
replaceNodeInEdgeWith n1 n2 =
    let replace n = if n == n1 then n2 else n
    in mapNodeInEdge replace

replaceNodeInLEdgeWith :: Node -> Node -> LEdge e -> LEdge e
replaceNodeInLEdgeWith n1 n2 =
    let replace n = if n == n1 then n2 else n
    in mapNodeInLEdge replace
