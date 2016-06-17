{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Calculi.Lambda.Cube.Systems.SystemF where

import           Data.Bifunctor.TH
import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Calculi.Lambda.Cube.Polymorphic
import           Calculi.Lambda.Cube.Typechecking
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens
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
    show (Mono m) = (show m)
    show (Poly p) =  show p
    show (Function a b) =
        let astr = if isFunction a || isJust (unquantify a) then "(" ++ show a ++ ")" else show a
        in  astr ++ " -> " ++ show b
    show (Forall p expr) =
        let getQuant :: SystemF m p -> ([p], SystemF m p)
            getQuant (Forall _p _expr) = getQuant _expr & _1 %~ (_p :)
            getQuant _expr             = ([], _expr)

            (ps, _expr) = getQuant expr
        in "forall " ++ show p ++ " " ++ unwords (show <$> ps) ++ ". " ++ show _expr

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
            m@Mono{}                     -> m
            p'@(Poly p)
                | p == target  -> sub
                | otherwise              -> p'
            Forall p expr
                | p == target -> applySubstitution' expr
                | otherwise              -> Forall p (applySubstitution' expr)
            Function fune arge           -> Function (applySubstitution' fune) (applySubstitution' arge)

    quantify = Forall
    unquantify (Forall a b) = Just (a, b)
    unquantify _ = Nothing

    poly = Poly

    freeTypeVariables = \case
        Mono _ -> Set.empty
        p@Poly{} -> Set.singleton p
        Forall p expr -> Set.delete (Poly p) (freeTypeVariables expr)
        Function l r -> freeTypeVariables l <> freeTypeVariables r

{-|
    Error sum not within Eithers because those (GHC) type errors are messy.
-}
data SystemFErr v t =
      SFNotKnownErr (NotKnownErr v t)
    | SFSimpleTypeErr (SimpleTypeErr t)
    | SFSubsErr (SubsErr Gr t (PolyType t))

deriving instance (Polymorphic t, Eq v) => Eq (SystemFErr v t)
deriving instance (Polymorphic t, Show v, Show t, Show (PolyType t)) => Show (SystemFErr v t)

data SystemFContext v t p = SystemFContext {
      _polyctx :: SubsContext t p
      -- ^ The context for Polymorphic related information
    , _stlcctx :: SimpleTypingContext v t
      -- ^ The context for Simply-typed related information.
} deriving (Eq, Ord, Show)

makeLenses ''SystemFContext

instance (Ord v, Ord m, Ord p) => Typecheckable v (SystemF m p) where

    type TypingContext v (SystemF m p) = (SystemFContext v (SystemF m p) p)

    -- Sum of NotKnownErr, SimpleTypeErr, and SubsErr, wrapped in ErrorContext
    type TypeError v (SystemF m p) =
        ErrorContext'
            v
            (SystemF m p)
            (SystemFErr v (SystemF m p))

    typecheck env _expr = runTypecheck env (typecheck' _expr) where
        {-
            Using a State type to pass around our environment
        -}
        typecheck' :: LambdaExpr v (SystemF m p) -> Typecheck v (SystemF m p) (SystemF m p)
        typecheck' __expr =
            -- Append the current expression to any ErrorContexts
            flip catchError (throwError . fmap (expression %~ (__expr :)))
            $ case __expr of
                Var v -> do
                    -- Query the type of the variable
                    t <- Map.lookup v <$> use (stlcctx.vars)
                    -- Nameerror action in case v doesn't exist within the typing context.
                    let nameErr = do {
                        -- Get the current environment
                        env' <- get;
                        -- throw the nameerror.
                        throwError [ErrorContext [] env' (SFNotKnownErr (UnknownVariable v))];
                    }
                    -- If v's type (t) is Nothing then nameerror, otherwise just return it.
                    maybe nameErr return t

                Apply fun arg -> do
                    fun'type <- typecheck' fun
                    arg'type <- typecheck' arg
                    -- Split fun'type into it's components
                    (fun'from, fun'to) <- case reify fun'type of
                        -- fun'type wasn't a function type, throw an error.
                        Nothing -> do
                            -- Get the environment
                            env' <- get
                            -- throw the type error
                            throwError [ErrorContext [fun] env' (SFSimpleTypeErr (NotAFunction fun'type))]
                        -- return the result
                        Just reified -> return reified

                    undefined

        {-
        x =
            -- Check that the argument type is the same or more specific than
            -- the type of the expected argument to fun.
            | from ⊑ arg'type -> do
                case substitutions arg'type from of
                    -- There was a mismatch in structure, this needs
                    -- to be thrown as an error.
                    Nothing -> do
                        env' <- get
                        let structErrs = uncurry UnexpectedType <$> mismatchErrs arg'type from
                        throwError $ ErrorContext [] env' . SFSimpleTypeErr <$> structErrs

                    Just subs -> case applyAllSubsGr subs of
                        Left subserrs -> do
                            env' <- get
                            throwError $ ErrorContext [] env' . SFSubsErr <$> subserrs

                        Right applySubs -> return applySubs -}

instance (Arbitrary m, Data m, Arbitrary p, Data p) => Arbitrary (SystemF m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized generatorP
