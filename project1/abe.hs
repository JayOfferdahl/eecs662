{-# LANGUAGE GADTs #-}

-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

-- Imports for PLIH
import ParserUtils

-- EECS 662 - Project 01
--
-- Author: Jay Offerdahl
-- Date: Tue Feb 21 2017 11:25:13 CDT 2017
--
-- A simple interpreter with support for arithmetic operations, limited conditionals, and an if
-- statement. Modified to use the Either monad to return errors with whatever I wanted to say. ;)


-- Abstract Syntax Tree Definition

data TABE where
    TNum :: TABE
    TBool :: TABE
    deriving (Show,Eq)

data ABE where
    Num :: Int -> ABE
    Plus :: ABE -> ABE -> ABE
    Minus :: ABE -> ABE -> ABE
    Mult :: ABE -> ABE -> ABE
    Div :: ABE -> ABE -> ABE
    Boolean :: Bool -> ABE
    And :: ABE -> ABE -> ABE
    Leq :: ABE -> ABE -> ABE
    IsZero :: ABE -> ABE
    If :: ABE -> ABE -> ABE -> ABE
    deriving(Show, Eq)


-- Parser (requires Parsec/ParseUtils -- from parseUtils.hs)

expr :: Parser ABE
expr = buildExpressionParser opTable term

opTable =   [
                [ inFix "*" Mult AssocLeft,
                  inFix "/" Div AssocLeft ],
                [ inFix "+" Plus AssocLeft,
                  inFix "-" Minus AssocLeft ],
                [ inFix "<=" Leq AssocLeft,
                  preFix "isZero" IsZero ],
                [ inFix "&&" And AssocLeft ]    
            ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr


-- Parsec function to interpret an ABE data structure and return either an ABE value or error msg.
-- "Parser invocation"

parseABE = parseString expr
parseABEFile = parseFile expr

-- Eval Function

eval :: ABE -> (Either String ABE)
eval (Num x) = (Right (Num x))
eval (Plus l r) = 
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Num v1)) -> case (eval r) of
                                (Left e) -> (Left e)
                                (Right (Num v2)) -> (Right (Num (v1 + v2)))
                                (Right _) -> (Left "Error: Type error mismatch in Plus.")
        (Right _) -> (Left "Error: Type error mismatch in Plus.")
eval (Minus l r) = 
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Num v1)) -> case (eval r) of
                                (Left e) -> (Left e)
                                (Right (Num v2)) -> (Right (Num (v1 - v2)))
                                (Right _) -> (Left "Error: Type error mismatch in Minus.")
        (Right _) -> (Left "Error: Type error mismatch in Minus.")
eval (Mult l r) =
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Num v1)) -> case (eval r) of
                                (Left e) -> (Left e)
                                (Right (Num v2)) -> (Right (Num (v1 * v2)))
                                (Right _) -> (Left "Error: Type error mismatch in Mult.")
        (Right _) -> (Left "Error: Type error mismatch in Mult.")
eval (Div l r) =
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Num v1)) -> case (eval r) of
                                (Left e) -> (Left e)
                                (Right (Num v2)) -> case (eval (IsZero (Num v2))) of
                                                        (Left e) -> (Left e)
                                                        (Right (Boolean True)) -> (Left "Error: Attempted division by zero.")
                                                        (otherwise) -> (Right (Num (div v1 v2)))
                                (Right _) -> (Left "Error: Type error mismatch in Div.")
        (Right _) -> (Left "Error: Type error mismatch in Div.")
eval (Boolean x) = (Right (Boolean x))
eval (IsZero x) =
    case (eval x) of
        (Left e) -> (Left e)
        (Right (Num y)) -> (Right (Boolean (y == 0)))
        (Right _) -> (Left "Error: Type error mismatch in IsZero.")
eval (And l r) =
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Boolean v1)) -> case (eval r) of
                                    (Left e) -> (Left e)
                                    (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                                    (Right _) -> (Left "Error: Type error mismatch in And.")
        (Right _) -> (Left "Error: Type error mismatch in And.")
eval (Leq l r) =
    case (eval l) of
        (Left e) -> (Left e)
        (Right (Num v1)) -> case (eval r) of
                                (Left e) -> (Left e)
                                (Right (Num v2)) -> (Right (Boolean (v1 <= v2)))
                                (Right _) -> (Left "Error: Type error mismatch in Leq.")
        (Right _) -> (Left "Error: Type error mismatch in Leq.")
eval (If c t e) =
    case (eval c) of
        (Left e) -> (Left e)
        (Right (Boolean v1)) -> case v1 of
                                    (True) -> (eval t)
                                    (False) -> (eval e)
        (Right _) -> (Left "Error: Type error mismatch in If.")


-- Typeof Derivation Functions

typeof :: ABE -> Either String TABE
typeof (Num x) = (Right TNum)
typeof (Plus l r) = let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TNum)
                        else Left "Type error mismatch in Plus."
typeof (Minus l r) = let l' = (typeof l)
                         r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TNum)
                        else Left "Type error mismatch in Minus."
typeof (Mult l r) = let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TNum)
                        else Left "Type error mismatch in Mult."
typeof (Div l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then case (eval (IsZero r)) of
                                (Left e) -> (Left e)
                                (Right (Boolean True)) -> (Left "Constant 0 found in denominator.")
                                (Right (Boolean False)) -> (Right TNum)
                        else Left "Type error mismatch in Div."
typeof (Boolean b) = (Right TBool)
typeof (IsZero x) = let x' = (typeof x)
                    in if x' == (Right TNum)
                        then (Right TBool)
                        else Left "Type error mismatch in IsZero."
typeof (And l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TBool) && r' == (Right TBool)
                        then (Right TBool)
                        else Left "Type error mismatch in And."
typeof (Leq l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TBool)
                        else Left "Type error mismatch in Leq."
typeof (If c t e) = let c' = (typeof c)
                        t' = (typeof t)
                        e' = (typeof e)
                    in if c' == (Right TBool) && t' == e'
                        then t'
                        else Left "Type error mismatch in If."


-- Interpreter

interp :: String -> Either String ABE
interp statement =  let e = (parseABE statement) in
                        case (typeof e) of
                            (Left err) -> (Left err)
                            (Right _) -> (eval (optimize e))


-- Code optimizer which replaces a few cases of silly statements such as "x + 0" or if true...

optimize :: ABE -> ABE
optimize (Plus l r) = case (eval (IsZero r)) of
                        (Right (Boolean True)) -> (l)
                        (Right (Boolean False)) -> (Plus l r)
optimize (If c t e) = case c of
                        (Boolean True) -> (t)
                        (Boolean False) -> (e)
                        (_) -> (If c t e)