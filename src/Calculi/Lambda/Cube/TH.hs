{-# LANGUAGE CPP #-}
module Calculi.Lambda.Cube.TH (
     -- sfo
      sf
    , stlc
) where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Compiler.Typesystem.SystemFOmega as SFO
import qualified Compiler.Typesystem.SystemF as SF
import qualified Compiler.Typesystem.SimplyTyped as STLC
import Text.Megaparsec
import Text.Megaparsec.Error
import Calculi.Lambda.Cube
import Data.List
import Control.Monad

-- | Lambda Cube parsec type.
#if MIN_VERSION_megaparsec(5,0,0)
type LCParsec = Parsec Dec String
#else
type LCParsec = Parsec String
#endif
-- | SystemFOmega with mono and poly types represented as strings.
-- type StringSFO = SFO.SystemFOmega String String (Maybe (STLC.SimplyTyped String))
-- | SystemF with mono and poly types represented as strings.
type StringSF = SF.SystemF String String
-- | SimplyTyped with mono types represented as strings.
type StringSTLC = STLC.SimplyTyped String

{-|
    Lambda Cube symbol wrapper for strings.
-}
lamcsymbol :: String -> LCParsec String
lamcsymbol = lamctoken . string

{-|
    Lambda Cube parser token wrapper, expects the token followed by 0 or more spaces.
-}
lamctoken :: LCParsec a -> LCParsec a
lamctoken p = do
    pval <- p
    void $ many (char ' ')
    return pval

{-|
    Parenthesis parser combinator.
-}
paren :: LCParsec a -> LCParsec a
paren = between (lamcsymbol "(") (lamcsymbol ")")

{-|
    Wrapper that allows preceeding whitespace before a token and then expects the
    input to end.
-}
wrapped :: LCParsec a -> LCParsec a
wrapped p = do
    void $ many (lamcsymbol " ")
    p' <- p
    eof
    return p'

{-|
    Parser for a bare variable, notated by beginning with a lowercase character.
-}
variable :: LCParsec String
variable = lamctoken ((:) <$> lowerChar <*> many (lowerChar <|> upperChar)) <?> "variable"

{-|
    Parser for a bare constant, notated by beginning with an uppercase character.
-}
constant :: LCParsec String
constant = lamctoken ((:) <$> upperChar <*> many (lowerChar <|> upperChar)) <?> "constant"

{-|
    given a subexpression parser, parse a sequence of subexpressions
    seperated by function arrows.
-}
exprsequence :: SimpleType t => LCParsec t -> LCParsec t
exprsequence subexpr = label "expression sequence" $ do
    -- parse as many subexpressions as we can (at least 1 though)
    expr <- subexpr
    -- optionally parse a function tail if it is present
    funApply <- optional $ do
        void $ lamcsymbol "->" <|> lamcsymbol "→"
        exprsequence subexpr
    -- if after the initial sequence it turned out this was the first
    -- argument to a function expression, then we apply it as the first argument.
    return (maybe expr (expr /->) funApply)
{-
sfoexpr :: LCParsec StringSFO
sfoexpr = label "System-Fω expression" $
           quant sfoexpr
       <|> exprsequence (fmap (foldl1 (/$)) <$> some $
                                    poly <$> variable
                                <|> mono <$> constant
                                <|> paren sfoexpr)
-}
sfexpr :: LCParsec StringSF
sfexpr = label "System-F expression" $
          exprsequence (typevar <$> variable
                    <|> typeconst <$> constant
                    <|> paren sfexpr)

stlcexpr :: LCParsec StringSTLC
stlcexpr = label "Simply-typed expression" $ exprsequence (typeconst <$> constant <|> paren stlcexpr)

{-
{-|
    A QuasiQuoter for SystemFOmega, allowing arbitrary type application

    @[sfo| forall x. R x -> M x |] == quantify \"x\" (mono \"R\" /$ poly \"x\" /-> mono \"M\" /$ poly \"x\")@
-}
sfo :: TH.QuasiQuoter
sfo = mkqq "sfo" sfoexpr
-}
{-|
    A QuasiQuoter for SystemF, allowing quantification and poly types (lower case).

    @[sf| forall a b. a -> b |] == quantify \"a\" (quantify \"b\" (poly \"a\" \/-> poly \"b\"))@

-}
sf :: TH.QuasiQuoter
sf   = mkqq "sf" sfexpr

{-|
    A QuasiQuoter for SimplyTyped.

    @[stlc| A -> B -> C |] == mono \"A\" \/-> mono \"B\" \/-> mono \"C\"@

    @[stlc| (A -> B) -> B |] == (mono \"A\" \/-> mono \"B\") \/-> mono \"B\"@
-}
stlc :: TH.QuasiQuoter
stlc = mkqq "stlc" stlcexpr

{-|
    Helper to generate a QuasiQuoter for an arbitrary parser with a liftable type.
-}
mkqq :: TH.Lift t => String -> LCParsec t -> TH.QuasiQuoter
mkqq pname p = TH.QuasiQuoter {
    TH.quoteExp = \str -> do
        loc <- TH.location
        let fname = intercalate ":" [pname
                                    , TH.loc_filename loc
                                    , show $ TH.loc_start loc
                                    , show $ TH.loc_end loc
                                    ]
        case runParser (wrapped p) fname str of
            Left err -> fail . show $ err
            Right val -> TH.lift val
    , TH.quotePat = error $ pname ++ " doesn't implement quotePat for this QuasiQuoter"
    , TH.quoteType = error $ pname ++ " doesn't implement quoteType for this QuasiQuoter"
    , TH.quoteDec = error $ pname ++ " doesn't implement quoteDec for this QuasiQuoter"
}
