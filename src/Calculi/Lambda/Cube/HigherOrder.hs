{-# LANGUAGE FlexibleContexts #-}
module Calculi.Lambda.Cube.HigherOrder where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Typechecking
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
    The representation to be typechecked at the kind level.
-}
type Kindedness t = LambdaTerm t () (Kindsystem t)

{-|
    Typeclass for higher-order types.
-}
class (Typecheckable t () (Kindsystem t), SimpleType t) => HigherOrder t where
    {-|
        The representation of kind constants.
    -}
    type Kindsystem t :: *

    {-|
        Construct a kind expression describing the application and abstraction of
        types in a given type. Not given a kind enviroment as given a kindedness
        expression, this information can be derived generally.

        @`kind` (∀ a. a) = (Lambda (a, star) a)@

        If inference elsewhere found out that @(∀ a. a)@'s kind wasn't @*@ and instead
        @* → *@ then it could rewrite this expression to match. What matters is that
        the type is in a form that can be manipulated and checked in a general manner.
    -}
    kind :: t -> Kindedness t

    {-|
        Translate a kindedness expression back to a type, functionally the inverse of
        `kind`.
    -}
    unkind :: Kindedness t -> Maybe t

    {-|
        More generalised form of `abstract` to work on all type operators, not
        just function types.

        @`typeap` M (∀a. a) = (∀ a. M a)@

        @`typeap` T X       = (T X)@

        @`typeap` (`typeap` ((→)) A) B ≡ `abstract` A B@
    -}
    typeap :: t -> t -> t

    {-|
        More generalised form of `reify`, working on all type application.

        @`untypeap` (M x)   = Just (M, x)@

        @`untypeap` (X → Y) = Just (((→) X), Y)@

        @`untypeap` X       = Nothing@
    -}
    untypeap :: t -> Maybe (t, t)
    untypeap x = case kind x of
        Apply a b -> (,) <$> unkind a <*> unkind b
        _         -> Nothing

{-|
    Typecheck a type expression's kindedness.
-}
kindcheck :: forall t ksys. (Kindsystem t ~ ksys, HigherOrder t)
          => TypingContext t () ksys                -- ^ A typing context for typechecking
          -> t                                      -- ^ A type expression to kindcheck
          -> Either [TypeError t () ksys]
                    (TypingContext t () ksys, ksys) -- ^ The result.
kindcheck ctx texpr = typecheck ctx (kind texpr)

{-|
    Infix `typeap`.
-}
(/$) :: (HigherOrder t) => t -> t -> t
(/$) = typeap
infixl 8 /$

{-|
    Shorthand for the constant `Star` in typesystems.
-}
star :: (SimpleType t, MonoType t ~ Star) => t
star = mono Star
