module Calculi.Lambda.Cube.HigherOrder where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Systems.SimplyTyped as SimplyTyped
import qualified Data.Map                                as Map

type KindEnvironment t = Map.Map t (Kindedness t)

{-|
    The type constants for higher-order typed lambda calculus.
-}
data Star =
      Star
    -- ^ The kind constant "@*@".
    deriving (Eq, Ord, Show, Read)

{-|
    Simply-typed lambda calculus at the type level, describing the
    kindedness of a type expression and used to typecheck/infer
-}
type Kindedness t = LambdaExpr t (SimplyTyped Star)

{-|
    Typeclass for higher-order types.
-}
class SimpleType t => HigherOrder t where

    {-|
        Construct a kind expression describing the application and abstraction of
        types in a given type. Not given a kind enviroment as given a kindedness
        expression, this information can be derived generally.

        @`kind` (∀ a. a) = Let [(a, Var a `star`)] (Var a)@

        If inference elsewhere found out that @(∀ a. a)@'s kind wasn't @*@ and instead
        @* → *@ then it could rewrite this expression to match. What matters is that
        the type is in a form that can be manipulated and checked in a general manner.
    -}
    kind :: t -> Kindedness t

    {-|
        Translate a kindedness expression back to a type, functionally the inverse of
        `kind`.
    -}
    unkind :: Kindedness t -> t

    {-|
        More generalised form of `abstract` to work on all type operators, not
        just function types.

        @`applyType` M (∀a. a) = (∀ a. M a)@

        @`applyType` T X       = (T X)@

        @`applyType` (`applyType` ((→)) A) B ≡ `abstract` A B@
    -}
    applyType :: t -> t -> t
    applyType a b = unkind (Apply (kind a) (kind b))

    {-|
        More generalised form of `reify`, working on all type application.

        @`dissectType` (M x)   = Just (M, x)@

        @`dissectType` (X → Y) = Just (((→) X), Y)@

        @`dissectType` X       = Nothing@
    -}
    dissectType :: t -> Maybe (t, t)
    dissectType x = case kind x of
        Apply a b -> Just (unkind a, unkind b)
        _         -> Nothing

    {-# MINIMAL kind, unkind #-}

{-|
    Infix `applyType`.
-}
($^) :: (HigherOrder t) => t -> t -> t
($^) = applyType
infixl 8 $^

{-|
    Shorthand for @`SimplyTyped.Mono` `Star`@ which can look messy in implementations.
-}
star :: SimplyTyped Star
star = SimplyTyped.Mono Star
