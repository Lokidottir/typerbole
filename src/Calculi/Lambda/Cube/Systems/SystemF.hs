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
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Random.Generics
import           Data.Generics
import           Data.Monoid
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
    deriving (Eq, Ord, Show, Read, Data)

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

    substitutions = curry $ \case
        (Forall _ expr, target) -> substitutions expr target
        (expr, Poly p)   -> Just [(expr, p)]
        (expr, Forall _ target) -> substitutions expr target
        (Function fune arge, Function funt argt)
                                -> (<>) <$> substitutions fune funt <*> substitutions arge argt
        (expr, target)
            | expr == target -> Just []
            | otherwise      -> Nothing

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

instance (Ord v, Ord m, Ord p) => Typecheckable v (SystemF m p) where

    -- Product of TypingEnvironment and SubsContext as our typing context
    type TypingContext v (SystemF m p) = (SimpleTypingContext v (SystemF m p), SubsContext' (SystemF m p))

    -- Sum of NotKnownErr, SimpleTypeErr, and SubsErr, wrapped in ErrorContext
    type TypeError v (SystemF m p) =
        ErrorContext'
            v
            (SystemF m p)
            (SystemFErr v (SystemF m p))

    typecheck env _expr = runTypecheck env (typecheck' _expr) where
        {-
            Using a State type to pass around our environment as parts of
        -}
        typecheck' :: LambdaExpr v (SystemF m p) -> Typecheck v (SystemF m p) (SystemF m p)
        typecheck' __expr =
            -- Append the current expression to any ErrorContexts
            flip catchError (throwError . fmap (expression %~ (__expr :)))
            $ case __expr of
                Var v ->
                    let nameErr = get >>= (\env -> throwError [ErrorContext [] env (SFNotKnownErr (UnknownVariable v))])
                    in do
                        x <- (Map.lookup v <$> use (_1.vars))
                        maybe nameErr return x

instance (Arbitrary m, Data m, Arbitrary p, Data p) => Arbitrary (SystemF m p) where
    -- TODO: remove instances of Data for m and p
    arbitrary = sized generatorP
