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
import           Data.Either.Validation as Val
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
import qualified Term.Unify as Unify
import qualified Language.Haskell.TH.Lift as TH

{-|
    An implementation of System-F, similar to haskell's own typesystems but without
    type-level functions beyond (→)
-}
data SystemF c v =
      TypeCon c
      -- ^ TypeCon types/type constants, i.e. @Int@ or @String@
    | TypeVar v
      -- ^ Poly types/type variables, i. e. the @a@ a -> Int@
    | Function (SystemF c v) (SystemF c v)
      -- ^ Function type constructor, i e. @->@ in @a -> b@
    deriving (Eq, Ord, Data)

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
        show' (TypeCon m) = show m
        show' (TypeVar p) = show p
        show' (Function a b) =
            let astr = if isFunction a then "(" ++ show' a ++ ")" else show' a
            in  astr ++ " -> " ++ show' b

deriveBifunctor ''SystemF
deriveBifoldable ''SystemF
deriveBitraversable ''SystemF
TH.deriveLift ''SystemF

instance (Ord m, Ord p) => SimpleType (SystemF m p) where

    type TypeConstant (SystemF m p) = m

    abstract = Function

    typeconst = TypeCon

    equivalent = Unify.areAlphaEquivalent

instance (Ord m, Ord p) => SimplyTypedUtil (SystemF m p) where
    unabstract (Function a b) = Just (a, b)
    unabstract _              = Nothing

    bases = \case
        Function fun arg -> bases fun <> bases arg
        expr             -> Set.singleton expr

instance (Ord m, Ord p) => Unify.Unifiable (SystemF m p) where

    type Variable (SystemF m p) = p

    variable = typevar

    vars = \case
        TypeVar p -> Set.singleton p
        Function a b -> Unify.vars a <> Unify.vars b
        _ -> Set.empty

    type Constant (SystemF m p) = m

    constant = typeconst

    consts = \case
        TypeCon m -> Set.singleton m
        Function a b -> Unify.consts a <> Unify.consts b
        _ -> Set.empty

    applySubstitution target _substitution =
        let
            substitution = Unify.applySubstitution target _substitution _substitution
            _applySubstitution = Unify.applySubstitution target substitution
        in \case
            ply@(TypeVar p)
                | p == target -> substitution
                | otherwise -> ply
            Function a b -> Function (_applySubstitution a) (_applySubstitution b)
            term -> term

    disagreements a b =
        let _disagreements = curry $ \case
                (TypeVar p1, TypeVar p2) -> Val.Success $ Set.singleton (Unify.Alias p1 p2)
                (TypeVar p , term)    -> Val.Success $ Set.singleton (Unify.Substitution p term)
                (term   , TypeVar p)  -> Val.Success $ Set.singleton (Unify.Substitution p term)
                (Function a1 b1, Function a2 b2) -> (<>) <$> _disagreements a1 a2 <*> _disagreements b1 b2
                (term1, term2)
                    | term1 == term2 -> Val.Success Set.empty
                    | otherwise -> Val.Failure [(term1, term2)]
        in validationToEither (_disagreements a b)

instance (Ord m, Ord v) => Polymorphic (SystemF m v) where

    type UnifyContext (SystemF m v) = ()

    type UnifyError (SystemF m v) = Unify.FirstOrderSubsError Gr (SystemF m v) v

    unify _ t1 t2 = ((), Unify.unifier t1 t2)

    type TypeVariable (SystemF m v) = v

    typevar = TypeVar

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
    arbitrary = sized (generatorSRWith aliases) where
        aliases :: [AliasR Gen]
        aliases = [
                    aliasR (\() -> arbitrary :: Gen m)
                  , aliasR (\() -> arbitrary :: Gen p)
                  ]
