{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Compiler.Typesystem.SystemF where

import           Data.Bifunctor.TH
import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.Polymorphic.Unification
import           Calculi.Lambda.Cube.Typechecking
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens hiding (elements)
import           Data.Either.Combinators
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Traversable
import           Data.List
import           Data.Random.Generics
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
    | Poly p
    | Function (SystemF m p) (SystemF m p)
    | Forall p (SystemF m p)
    deriving (Eq, Ord, Data)

instance (Ord m, Ord p, Show m, Show p) => Show (SystemF m p) where
    show (Mono m) = show m
    show (Poly p) =  show p
    show (Function a b) =
        let isForall (Forall _ _) = True
            isForall _ = False
            astr = if isFunction a || isForall a then "(" ++ show a ++ ")" else show a
        in  astr ++ " -> " ++ show b
    show (Forall p expr) =
        let getQuant :: SystemF m p -> ([p], SystemF m p)
            getQuant (Forall _p _expr) = getQuant _expr & _1 %~ (_p :)
            getQuant _expr             = ([], _expr)
            (ps, _expr) = getQuant expr
        in "forall " ++ unwords (show <$> (p:ps)) ++ ". " ++ show _expr


deriveBifunctor ''SystemF
deriveBifoldable ''SystemF
deriveBitraversable ''SystemF
TH.deriveLift ''SystemF

instance (Ord m, Ord p) => SimpleType (SystemF m p) where

    type MonoType (SystemF m p) = m

    abstract = Function

    reify (Function a b) = Just (a, b)
    reify _              = Nothing

    bases = \case
        Function fun arg -> bases fun <> bases arg
        Forall p expr    -> Set.insert (Poly p) (bases expr)
        expr             -> Set.singleton expr

    mono = Mono

    equivalent = areAlphaEquivalent

instance (Ord m, Ord p) => Polymorphic (SystemF m p) where

    type PolyType (SystemF m p) = p

    substitutions =
        let (<><>) :: (Semigroup s1, Semigroup s2) => Either s1 s2 -> Either s1 s2 -> Either s1 s2
            (<><>) = curry $ \case
                (Left a, Left b) -> Left (a <> b)
                (a, b) -> (<>) <$> a <*> b
        in curry $ \case
            (Forall _ expr1    , expr2)              -> substitutions expr1 expr2
            (expr1             , Forall _ expr2)     -> substitutions expr1 expr2
            (Poly p1           , Poly p2)            -> Right [Mutual p1 p2]
            (expr              , Poly p)             -> Right [Substitution expr p]
            (Poly p            , expr)               -> Right [Substitution expr p]
            (Function arg1 ret1, Function arg2 ret2) -> substitutions arg1 arg2 <><> substitutions ret1 ret2
            (expr1             , expr2)
                | expr1 == expr2 -> Right []
                | otherwise      -> Left [(expr1, expr2)]

    applySubstitution sub target = applySubstitution' where
        applySubstitution' = \case
            m@Mono{}           -> m
            p'@(Poly p)
                | p == target  -> sub
                | otherwise    -> p'
            Forall p expr
                | p == target  -> applySubstitution' expr
                | otherwise    -> Forall p (applySubstitution' expr)
            Function from to -> Function (applySubstitution' from) (applySubstitution' to)

    quantify = Forall

    poly = Poly

    quantifiedOf = \case
        Mono _ -> Set.empty
        Poly _ -> Set.empty
        Function from to -> quantifiedOf from <> quantifiedOf to
        Forall p texpr -> Set.insert (poly p) (quantifiedOf texpr)

    polytypesOf = \case
        Mono _ -> Set.empty
        p@Poly{} -> Set.singleton p


{-|
    Error sum not within Eithers because those (GHC) type errors are messy.
-}
data SystemFErr c v t =
      SFNotKnownErr (NotKnownErr c v t)
    | SFSimpleTypeErr (SimpleTypeErr t)
    | SFSubsErr (SubsErr Gr t (PolyType t))

deriving instance (Polymorphic t, Eq v, Eq c) => Eq (SystemFErr c v t)
deriving instance (Polymorphic t, Show v, Show c, Show t, Show (PolyType t)) => Show (SystemFErr c v t)

data SystemFContext c v t p = SystemFContext {
      _polyctx :: SubsContext t p
      -- ^ The context for Polymorphic related information
    , _stlcctx :: SimpleTypingContext c v t
      -- ^ The context for Simply-typed related information.
} deriving (Eq, Ord, Show)

makeLenses ''SystemFContext

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
                    (fun'from, fun'to) <- case reify fun'type of
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
        process = generalise' . massUnquantify where
            {-
                Actually, remove all quantifications as we don't actually care about them during
                substitution, which is most of what's getting tested.

                Also SystemF doesn't do existential quantification by default (probably?)
            -}
            massUnquantify :: SystemF m p -> SystemF m p
            massUnquantify t@Mono{} = t
            massUnquantify t@Poly{} = t
            massUnquantify (Function from to) = massUnquantify from /-> massUnquantify to
            massUnquantify (Forall _ texpr) = massUnquantify texpr
