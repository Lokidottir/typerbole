{-# LANGUAGE ScopedTypeVariables #-}
module Calculi.Lambda.Cube.Polymorphic where

import           Calculi.Lambda.Cube.SimpleType
import           Data.Either
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Helper
import           Data.List.Ordered
import qualified Data.Map                       as Map
import           Data.Maybe
import qualified Data.Set                       as Set
import           Data.Tuple

type Substitution t = t -> t

-- TODO: Maybe rename the constructors and recomment
data SubsError t =
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

{-|
    Class of typesystems that exhibit polymorphism.
-}
class SimpleType t => Polymorphic t where
    {-|
        Generates a list of tuples representing the possible substitutions that
        can be made when the first type is substituting the second.

        Doesn't have to be checked within this function, as subsToGraph performs
        a significant amount of analysis that is used in `canSubstitute`'s default
        implementation.

        @`substitutions` (T → G) (∀ a. (∀ b. a → b)) = Just [(T, a), (G, b)]@

        @`substitutions` (∀ a. a -> a) (∀ b. b) = Just [(a -> a, b)]@
    -}
    substitutions :: t -> t -> Maybe [(t, t)]

    {-|
        Substitution application, given one type substituting another, generate a function
        that will apply this substitution to a given type.
    -}
    applySubstitution :: t -> t -> Substitution t

    {-|
        Calculate if one type can substitute another, should check if there are any error in the
        substitutions such as cycles or multiple possible substitutions, then return true if
        either both are identical or the substitutions don't conflict.

        This is a lot to ask for, thankfully this is already implemented in terms of
        `substitutions` and `subsToGraph`, this is here in case there's a more efficient
        algorithm the library user knows about.

        Note that this may need renaming, as ()
    -}
    canSubstitute :: t -> t -> Bool
    canSubstitute x y =
        -- NOTE: This doesn't work as implied by it's name on @canSubstitute (a → K) (M → b)@
        -- but it this is still valid as far as type theory (and ghci) is concerned
        fromMaybe False (isRight . subsToGraph <$> substitutions x y) || x == y

    {-
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

    {-# MINIMAL substitutions, applySubstitution #-}

{-|
    Infix, flipped `canSubstitute` corresponding to the type ordering operator used in
    much of type theory.
-}
(⊑) :: Polymorphic t => t -> t -> Bool
(⊑) = flip canSubstitute

infix 6 ⊑

{-|
    Infix `areEquivalent`
-}
(≣) :: Polymorphic t => t -> t -> Bool
(≣) = areEquivalent

infix 6 ≣

{-|
    Given a list of substitutions, i.e. the output of `substitutions`, generate a graph
    if there are no cycles or clashes, otherwise return the errors relating to those.

    TODO: define clashes outside of the internal comments for this function.
    TODO: use fgl's nodemap functionality instead of the hacks that were used here.
-}
subsToGraph :: forall t. SimpleType t => [(t, t)] -> Either [SubsError (t, t)] (Gr (t, t) ())
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
