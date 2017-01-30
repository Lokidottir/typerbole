{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Compiler.Typesystem.SimplyTyped (
    SimplyTyped(..)
) where

import           Calculi.Lambda
import           Calculi.Lambda.Cube.SimpleType
import           Control.Typecheckable.PureTypecheckable
import           Control.Arrow ((>>>))
import           Control.Monad
import           Control.Lens
import qualified Control.Monad.State            as State
import qualified Control.Monad.Except           as Except
import qualified Control.Unification            as U
import qualified Data.List.NonEmpty             as NE
import           Data.Bifunctor
import           Data.Generics
import qualified Data.Map                       as Map
import           Generic.Random.Data
import           Data.Semigroup
import qualified Data.Set                       as Set
import           Test.QuickCheck
import qualified Language.Haskell.TH.Lift       as TH
import           Data.Either.Validation
import           Data.Functor.Fixedpoint

{-|
    Data type describing a type system for simply-typed lambda calculus (λ→).
-}
data SimplyTyped c
    = TypeCon c
    | Function (SimplyTyped c) (SimplyTyped c)
    deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

-- | Inference intermediate for use with `unification-fd`
data SimplyTypedII c ii
    = TypeConII c
    | FunctionII ii ii
    deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

toIntermediate :: SimplyTyped c -> Fix (SimplyTypedII c)
toIntermediate = \case
    TypeCon c -> Fix (TypeConII c)
    Function a b -> Fix (toIntermediate a `FunctionII` toIntermediate b)

fromIntermediate :: Fix (SimplyTypedII c) -> SimplyTyped c
fromIntermediate = unFix >>> \case
    TypeConII c -> TypeCon c
    FunctionII a b -> fromIntermediate a `Function` fromIntermediate b

instance Eq c => U.Unifiable (SimplyTypedII c) where
    zipMatch t1 t2 = case (t1, t2) of
        (TypeConII c1, TypeConII c2)
            | c1 == c2 -> Just (TypeConII c1)
            | otherwise -> Nothing
        (FunctionII a b, FunctionII c d) -> Just $ Right (a, c) `FunctionII` Right (b, d)
        _ -> Nothing

TH.deriveLift ''SimplyTyped

instance Ord m => SimpleType (SimplyTyped m) where
    type TypeConstant (SimplyTyped m) = m

    abstract = Function

    typeconst = TypeCon

    equivalent = (==)

instance Ord m => SimplyTypedUtil (SimplyTyped m) where

    unabstract (Function from to) = Just (from, to)
    unabstract _                  = Nothing

    bases (TypeCon c)           = Set.singleton (TypeCon c)
    bases (Function from to) = bases from `Set.union` bases to

data SimplyTypedErr c v t =
      STNotKnownErr (NotKnownErr c v t)
    | STSimpleTypeErr (SimpleTypeErr t)
    deriving (Eq, Ord, Show)

instance (Ord termcon, Ord var, Ord typecon) => PureTypecheckable (LambdaTerm termcon var) (SimplyTyped typecon) where

    type TypeError (LambdaTerm termcon var) (SimplyTyped typecon)
        = NE.NonEmpty (SimplyTypedErr termcon var (SimplyTyped typecon))

    type TypingContext (LambdaTerm termcon var) (SimplyTyped typecon)
        = SimpleTypingContext termcon var (SimplyTyped typecon)

    typecheckP term ctx = Except.runExcept $ State.runStateT (typecheckP_ term) ctx where
        typecheckP_ :: forall t term tyctx tyerr m.
                    -- Make lots of aliases so types are readable
                    ( t ~ (SimplyTyped typecon)
                    , term ~ (LambdaTerm termcon var)
                    , tyctx ~ TypingContext term t
                    , tyerr ~ TypeError term t
                    , m ~ State.StateT tyctx (Except.Except tyerr)
                    )
                    => term t
                    -> m t
        typecheckP_ = typecheckP_final where

            -- | lookup the type of a variable, or report an error
            varlookup :: var -> m t
            varlookup var = State.gets (Map.lookup var . _variables) >>= \case
                Nothing -> Except.throwError $ pure (STNotKnownErr (UnknownVariable var))
                Just t -> return t

            -- | lookup the type of a constant, or report an error
            constlookup :: termcon -> m t
            constlookup con = State.gets (Map.lookup con . _constants) >>= \case
                Nothing -> Except.throwError $ pure (STNotKnownErr (UnknownConstant con))
                Just t -> return t

            -- | get the type of the application of one term to another.
            termAp :: term t -> term t -> m t
            termAp f x = join $ deriveType <$> typecheckP_ f <*> typecheckP_ x where
                -- | derive the type of applying terms with the given types.
                deriveType :: t -> t -> m t
                deriveType f't x't = case f't of
                    a `Function` b
                        -- if a is the same as the type of x's type, then return b.
                        | a `equivalent` x't -> return b
                        | otherwise ->
                            Except.throwError $ pure (STSimpleTypeErr (UnexpectedType a x't))
                    -- 'f' is not a function
                    _ -> Except.throwError $ pure (STSimpleTypeErr (NotAFunction f't))

            lambda :: (var, t) -> term t -> m t
            lambda (v, t) term =
                withTempState (variables %~ Map.insert v t) $ (t /->) <$> typecheckP_ term where
                    -- Perform an action with a modified state, returning the
                    -- state to it's orginal form once the action is complete.
                    withTempState :: (tyctx -> tyctx) -> m a -> m a
                    withTempState f action = do
                        state <- State.get
                        State.modify f
                        result <- action
                        State.put state
                        return result

            typecheckP_final = \case
                Variable v -> varlookup v
                Constant c -> constlookup c
                Apply f x -> termAp f x
                Lambda declr term -> lambda declr term

instance (Ord termcon, Ord var, Ord typecon) => PureInferable (LambdaTerm termcon var) (SimplyTyped typecon) where

    type InferError (LambdaTerm termcon var) (SimplyTyped typecon)
        = TypeError (LambdaTerm termcon var) (SimplyTyped typecon)

    type InferContext (LambdaTerm termcon var) (SimplyTyped typecon)
        = TypingContext (LambdaTerm termcon var) (SimplyTyped typecon)

    inferP = undefined where
        inferP_ :: forall t it ut term tyctx tyerr m.
                -- Make lots of aliases so types are readable
                ( t ~ SimplyTyped typecon
                -- , it ~ SimplyTypedII typecon
                -- , ut ~ U.UTerm it
                , term ~ LambdaTerm termcon var
                , tyctx ~ InferContext term t
                , tyerr ~ InferError term t
                , m ~ State.StateT tyctx (Except.Except tyerr)
                )
                => term (Maybe t)
                -> m (term t)
        inferP_ = inferP_final <=< inferP_preprocess where

            -- | give all the untyped variables an index for their type.
            inferP_preprocess :: term (Maybe t) -> m (term (Either Integer t))
            inferP_preprocess = undefined

            inferP_final :: term (Either Integer t) -> m (term t)
            inferP_final = \case
                Variable v -> return $ Variable v
                Constant c -> return $ Constant c
                _ -> undefined

instance (Data m, Arbitrary m) => Arbitrary (SimplyTyped m) where
    arbitrary = sized $ generatorPWith [alias (\() -> arbitrary :: Gen m)]
