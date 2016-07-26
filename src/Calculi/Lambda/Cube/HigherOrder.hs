{-# LANGUAGE FlexibleContexts #-}
module Calculi.Lambda.Cube.HigherOrder where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Control.Typecheckable
import qualified Data.Map                                as Map

{-|
    Typeclass for higher-order types. Classically this would just be checking the
    <https://en.wikipedia.org/wiki/Arity arity> of type constructors but there are
    more complex typesystems that exist that could benefit from allowing an arbitrary
    typechecking ability for a higher-order typesystem.
-}
class (SimpleType t) => HigherOrder t where
    {-|
        The typesystem for the kindedness of type expressions.
    -}
    type Kindsystem t :: *

    {-|
        A typing context for the kindedness of type expressions. Analogue to `TypingContext`.
    -}
    type KindContext t :: *

    {-|
        Type errors for the kindedness of type expressions. Analogue to `TypeError`.
    -}
    type KindError t :: *

    {-|
        Typecheck a type expression.
    -}
    kindcheck :: KindContext t -> t -> Either [KindError t] (KindContext t, Kindsystem t)

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

{-|
    Infix `typeap`.
-}
(/$) :: (HigherOrder t) => t -> t -> t
(/$) = typeap
infixl 8 /$
