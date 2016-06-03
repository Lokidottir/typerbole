module Calculi.Lambda.Cube.TH (
      sfo
    , sf
    , stlc
) where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Calculi.Lambda.Cube.Systems.SystemFOmega as SFO
import qualified Calculi.Lambda.Cube.Systems.SystemF as SF
import qualified Calculi.Lambda.Cube.Systems.SimplyTyped as STLC
import Text.Megaparsec
import Calculi.Lambda.Cube
import Data.List
import Control.Monad

type LCParsec = Parsec String
type StringSFO = SFO.SystemFOmega String String
type StringSF = SF.SystemF String String
type StringSTLC = STLC.SimplyTyped String

lamcsymbol :: String -> LCParsec String
lamcsymbol str = do
    str' <- try $ string str
    void $ many (string " ")
    return str'

lamctoken :: LCParsec a -> LCParsec a
lamctoken p = do
    pval <- p
    void $ many (char ' ')
    return pval

paren :: LCParsec a -> LCParsec a
paren = between (lamcsymbol "(") (lamcsymbol ")")

wrapped :: LCParsec a -> LCParsec a
wrapped p = do
    void $ many (lamcsymbol " ")
    p' <- p
    eof
    return p'

variable :: LCParsec String
variable = lamctoken ((:) <$> lowerChar <*> many (lowerChar <|> upperChar)) <?> "variable"

constant :: LCParsec String
constant = lamctoken ((:) <$> upperChar <*> many (lowerChar <|> upperChar)) <?> "constant"

quant :: (Polymorphic t, String ~ PolyType t) => LCParsec t -> LCParsec t
quant pexpr = label "quantification" $ do
    void $ lamcsymbol "∀" <|> lamcsymbol "forall"
    tvars <- some variable
    void $ lamcsymbol "."
    expr <- pexpr
    return (foldr quantify expr tvars)

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

sfoexpr :: LCParsec StringSFO
sfoexpr = label "System-Fω expression" $
           paren sfoexpr
       <|> quant sfoexpr
       <|> exprsequence (fmap (foldl1 (/$)) <$> some $
                                    poly <$> variable
                                <|> mono <$> constant
                                <|> paren sfoexpr)

sfexpr :: LCParsec StringSF
sfexpr = label "System-F expression" $
          paren sfexpr
      <|> quant sfexpr
      <|> exprsequence (poly <$> variable
                           <|> mono <$> variable
                           <|> paren sfexpr)

stlcexpr :: LCParsec StringSTLC
stlcexpr = many (lamcsymbol " ")
        >> exprsequence (mono <$> constant <|> paren stlcexpr)
        <?> "Simply-typed expression"


{-|
    A QuasiQuoter for SystemFOmega, allowing arbitrary type application
-}
sfo :: TH.QuasiQuoter
sfo = mkqq "sfo" sfoexpr

{-|
    A QuasiQuoter for SystemF, allowing quantification and type variables (lower case).

    @[sf| forall a b. a -> b |] == quantify \"a\" (quantify \"b\" (Poly \"a\" \/-> Poly \"b\"))@

-}
sf :: TH.QuasiQuoter
sf   = mkqq "sf" sfexpr

{-|
    A QuasiQuoter for SimplyTyped.

    @[stlc| A -> B -> C |] == Mono \"A\" \/-> Mono \"B\" \/-> Mono \"C\"@

    @[stlc| (A -> B) -> B |] == (Mono \"A\" \/-> Mono \"B\") \/-> Mono \"B\"@
-}
stlc :: TH.QuasiQuoter
stlc = mkqq "stlc" stlcexpr

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
