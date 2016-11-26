{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Compiler.Typesystem.SystemF where

import           Data.Bifunctor.TH
import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Polymorphic
import           Control.Typecheckable
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens hiding (elements, from, to)
import           Data.Either.Combinators
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Traversable
import           Data.List
import           Generic.Random.Data
import           Data.Generics
import           Data.Semigroup
import           Data.Maybe
import           Data.Graph.Inductive (Gr)
import           Test.QuickCheck
import qualified Language.Haskell.TH.Lift as TH

{-|
    An implementation of System-F, similar to haskell's own typesystems but without
    type-level functions beyond (→)
-}
data SystemF m p =
      Mono m
      -- ^ Mono types/type constants, i.e. @Int@ or @String@
    | Poly p
      -- ^ Poly types/type variables, i. e. the @a@ in @forall a. a -> Int@
    | Function (SystemF m p) (SystemF m p)
      -- ^ Function type constructor, i e. @->@ in @a -> b@
    | Forall p (SystemF m p)
      -- ^ Universal quantifier, the @forall@ in @forall a. a@
    deriving (Eq, Ord, Data)

data Quant = Expr | Quantify deriving (Eq, Ord, Show, Read)

{-|
    First order logic System F representation.
-}
data SFGADT (q :: Quant) m p where
    SFMono :: m -> SFGADT 'Expr m p
    SFPoly :: p -> SFGADT 'Expr m p
    SFFunction :: SFGADT 'Expr m p -> SFGADT 'Expr m p -> SFGADT 'Expr m p
    SFForall :: [p] -> SFGADT q m p -> SFGADT 'Quantify m p

{-
{-|
    Error sum not within Eithers because those (GHC) type errors are messy.
-}
data SystemFErr c v t =
      SFNotKnownErr (NotKnownErr c v t)
    | SFSimpleTypeErr (SimpleTypeErr t)
    | SFSubsErr (SubsErr Gr t (PolyType t))


deriving instance (Polymorphic t, Eq v, Eq c) => Eq (SystemFErr c v t)
deriving instance (Polymorphic t, Show v, Show c, Show t, Show (PolyType t)) => Show (SystemFErr c v t)
-}
instance (Ord m, Ord p, Show m, Show p) => Show (SystemF m p) where
    show t = "[sf| " ++ show' t ++ " |]" where
        show' (Mono m) = show m
        show' (Poly p) = show p
        show' (Function a b) =
            let isForall (Forall _ _) = True
                isForall _ = False
                astr = if isFunction a || isForall a then "(" ++ show' a ++ ")" else show' a
            in  astr ++ " -> " ++ show' b
        show' (Forall p expr) =
            let getQuantified :: SystemF m p -> ([p], SystemF m p)
                getQuantified (Forall _p _expr) = getQuantified _expr & _1 %~ (_p :)
                getQuantified _expr             = ([], _expr)
                (ps, _expr) = getQuantified expr
            in "forall " ++ unwords (show <$> (p:ps)) ++ ". " ++ show' _expr

deriveBifunctor ''SystemF
deriveBifoldable ''SystemF
deriveBitraversable ''SystemF
TH.deriveLift ''SystemF

instance (Ord m, Ord p) => SimpleType (SystemF m p) where

    type MonoType (SystemF m p) = m

    abstract a b = systemFRaiseQuantifiers $ Function a b

    mono = Mono

    equivalent = undefined -- areAlphaEquivalent

instance (Ord m, Ord p) => SimplyTypedUtil (SystemF m p) where
    unabstract (Function a b) = Just (a, b)
    unabstract _              = Nothing

    bases = \case
        Function fun arg -> bases fun <> bases arg
        Forall p expr    -> Set.insert (Poly p) (bases expr)
        expr             -> Set.singleton expr

instance (Ord m, Ord p) => Polymorphic (SystemF m p) where

    type UnifyError (SystemF m p) = ()

    unify = undefined

    type PolyType (SystemF m p) = p

    poly = Poly

{-
instance (Ord c, Ord v, Ord m, Ord p) => Typecheckable (LambdaTerm c v) (SystemF m p) where

    type TypingContext (LambdaTerm c v) (SystemF m p) = (SystemFContext c v (SystemF m p) p)

    type TypeError (LambdaTerm c v) (SystemF m p) =
        ErrorContext'
            (LambdaTerm c v)
            (SystemF m p)
            (SystemFErr c v (SystemF m p))

    typecheck env _expr = runTypecheck env (typecheck' _expr) where
        {-
            Using thhe
        -}
        typecheck' :: LambdaTerm c v (SystemF m p) -> Typecheck (LambdaTerm c v) (SystemF m p) (SystemF m p)
        typecheck' __expr =
            -- Append the current expression to any ErrorContexts
            flip catchError (throwError . fmap (expression %~ (__expr :)))
            $ case __expr of
                Variable v -> do
                    -- Query the type of the variable
                    t <- Map.lookup v <$> use (stlcctx.variables)
                    -- Nameerror action in case v doesn't exist within the typing context.
                    let nameErr = throwErrorContext [] (SFNotKnownErr (UnknownVariable v))
                    -- If v's type (t) is Nothing then nameerror, otherwise just return it.
                    maybe nameErr return t

                Constant c ->  do
                    -- Query the type of the constant
                    t <- Map.lookup c <$> use (stlcctx.constants)
                    -- Nameerror action in case c doesn't exist within the typing context.
                    let nameErr = throwErrorContext [] (SFNotKnownErr (UnknownConstant c))
                    -- If c's type (t) is Nothing then nameerror, otherwise just return it.
                    maybe nameErr return t

                Apply fun arg -> do
                    fun'type <- typecheck' fun
                    arg'type <- typecheck' arg
                    -- Split fun'type into it's components
                    (fun'from, fun'to) <- case unabstract fun'type of
                        -- fun'type wasn't a function type, throw an error.
                        Nothing -> throwErrorContext [fun] (SFSimpleTypeErr (NotAFunction fun'type))
                        -- return the result
                        Just reified -> return reified
                    case unify fun'from arg'type of
                        Left errs ->
                            -- If errors were encountered during unification, throw them.
                            throwErrorContexts ((,) [] . SFSubsErr <$> errs)
                        Right subs ->
                            -- If substitutions were unified, then apply them to the
                            -- return type of the function.
                            return $ unvalidatedApplyAllSubs subs fun'to

                Lambda (v, t) expr -> do
                    -- If there are any types in v's type expression that
                    -- do not appear in the typing context or are not declated
                    -- within it, throw errors for the unknown types.
                    unknownTypes <- calcUnknownTypes t <$> use (stlcctx.allTypes)
                    unless (null unknownTypes) (throwErrorContexts ((,) [] <$> unknownTypes))
                    -- save the current state in scope
                    oldstate <- get
                    -- Register the variable v to have the type t in the current state
                    -- and typecheck the lambda's body with that state.
                    stlcctx.variables %= Map.insert v t
                    -- Also register all the outmost declared poly types
                    stlcctx.allTypes %= (outmostDeclaredPolys t <>)
                    -- Typecheck the lambda's expression with this added information
                    expr'type <- typecheck' expr
                    -- Reset to the old state.
                    put oldstate
                    -- Return the type of this expression.
                    return (t /-> expr'type)

        calcUnknownTypes t types =
            SFNotKnownErr . UnknownType <$> Set.toList (Set.difference (bases t) types)

        outmostDeclaredPolys (Forall p texpr) = Set.insert (poly p) (outmostDeclaredPolys texpr)
        outmostDeclaredPolys _ = Set.empty
-}
instance (Ord m, Ord p, Arbitrary m, Data m, Arbitrary p, Data p) => Arbitrary (SystemF m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = process <$> sized (generatorSRWith aliases) where
        aliases :: [AliasR Gen]
        aliases = [
                    aliasR (\() -> arbitrary :: Gen m)
                  , aliasR (\() -> arbitrary :: Gen p)
                  ]

        {-
            Remove all generated quantifications and then generalise the expression's poly types.
        -}
        process = systemFMassUnquantify

{-|
    Internal function, makes sure all universal quantifiers appear at the \"top\" of
    the type expression.

    ===Behaviour

    * Incorrectly quantified type expression

        >>> systemFRaiseQuantifiers [sf| forall a b. a -> (forall c. b -> c) |]
        [sf| forall a b c. a -> b -> c |]

    * No quantifiers

        >>> systemFRaiseQuantifiers [sf| X |]
        [sf| X |]

    * Already correctly quantified.

        >>> systemFRaiseQuantifiers [sf| forall a b. a -> b |]
        [sf| forall a b. a -> b |]
-}
systemFRaiseQuantifiers :: (Ord m, Ord p) => SystemF m p -> SystemF m p
systemFRaiseQuantifiers = systemFMassUnquantify

{-|
    Remove all quantifications from a SystemF expression.
-}
systemFMassUnquantify :: (Ord m, Ord p) => SystemF m p -> SystemF m p
systemFMassUnquantify t@Mono{} = t
systemFMassUnquantify t@Poly{} = t
systemFMassUnquantify (Function from to) = Function (systemFMassUnquantify from) (systemFMassUnquantify to)
systemFMassUnquantify (Forall _ texpr) = systemFMassUnquantify texpr
