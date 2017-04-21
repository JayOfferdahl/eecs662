{-# LANGUAGE GADTs #-}

module Proj3Utils where

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

--
-- Project utilities for developing CFAE and CFBAE
-- interpreters.
--
-- Author: Perry Alexander
-- Date: 6 April 2017
--
-- Edited By: Jay Offerdahl
-- Date: 20 April 2017
--

-- CFAE AST Definition
data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Mult :: CFAE -> CFAE -> CFAE
  Div :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  deriving (Show,Eq)

-- Parser
expr :: Parser CFAE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Mult AssocLeft
            , inFix "/" Div AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          ]

numExpr :: Parser CFAE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

identExpr :: Parser CFAE
identExpr = do i <- identifier lexer
               return (Id i)

lambdaExpr :: Parser CFAE
lambdaExpr = do reserved lexer "lambda"
                i <- identifier lexer
                reserved lexer "in"
                e <- expr
                return (Lambda i e)

appExpr :: Parser CFAE
appExpr = do reserved lexer "app"
             e1 <- expr
             e2 <- expr
             return (App e1 e2)

ifExpr :: Parser CFAE
ifExpr = do reserved lexer "if0"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If0 c t e)

term = parens lexer expr
       <|> numExpr
       <|> identExpr
       <|> ifExpr
       <|> lambdaExpr
       <|> appExpr

-- Parser invocation
parseCFAE = parseString expr

parseCFAEFile = parseFile expr


-- Exercise 1
type EnvD = [(String, CFAE)]

evalDynCFAE :: EnvD -> CFAE -> CFAE
evalDynCFAE env (Num x) = (Num x)
evalDynCFAE env (Plus l r) = let (Num l') = (evalDynCFAE env l)
                                 (Num r') = (evalDynCFAE env r)
                             in (Num (l' + r'))
evalDynCFAE env (Minus l r) = let (Num l') = (evalDynCFAE env l)
                                  (Num r') = (evalDynCFAE env r)
                              in (Num (l' - r'))
evalDynCFAE env (Mult l r) = let (Num l') = (evalDynCFAE env l)
                                 (Num r') = (evalDynCFAE env r)
                             in (Num (l' * r'))
evalDynCFAE env (Div l r) = let (Num l') = (evalDynCFAE env l)
                                (Num r') = (evalDynCFAE env r)
                            in (Num (div l' r'))
evalDynCFAE env (Lambda i b) = (Lambda i b)
evalDynCFAE env (App f a) = let (Lambda i b) = (evalDynCFAE env f)
                                a' = (evalDynCFAE env a)
                            in (evalDynCFAE ((i, a'):env) b)
evalDynCFAE env (Id id) = case (lookup id env) of
                               Just x -> x
                               Nothing -> error "Undefined id."
evalDynCFAE env (If0 c t e) = let (Num c') = (evalDynCFAE env c)
                              in if c' == 0 then (evalDynCFAE env t) else (evalDynCFAE env e)

interpDynCFAE :: String -> CFAE
interpDynCFAE input = let parseString = (parseCFAE input)
                      in (evalDynCFAE [] parseString)


-- Exercise 2
data CFAEValue where
  NumV :: Int -> CFAEValue
  ClosureV :: String -> CFAE -> EnvS -> CFAEValue
  deriving (Show,Eq)

type EnvS = [(String, CFAEValue)]

evalStatCFAE :: EnvS -> CFAE -> CFAEValue
evalStatCFAE env (Num x) = (NumV x)
evalStatCFAE env (Plus l r) = let (NumV l') = (evalStatCFAE env l)
                                  (NumV r') = (evalStatCFAE env r)
                              in (NumV (l' + r'))
evalStatCFAE env (Minus l r) = let (NumV l') = (evalStatCFAE env l)
                                   (NumV r') = (evalStatCFAE env r)
                               in (NumV (l' - r'))
evalStatCFAE env (Mult l r) = let (NumV l') = (evalStatCFAE env l)
                                  (NumV r') = (evalStatCFAE env r)
                              in (NumV (l' * r'))
evalStatCFAE env (Div l r) = let (NumV l') = (evalStatCFAE env l)
                                 (NumV r') = (evalStatCFAE env r)
                             in (NumV (div l' r'))
evalStatCFAE env (Lambda i b) = (ClosureV i b env)
evalStatCFAE env (App f a) =  let (ClosureV i b e) = (evalStatCFAE env f)
                                  a' = (evalStatCFAE env a)
                              in evalStatCFAE ((i, a'):e) b
evalStatCFAE env (Id id) = case (lookup id env) of
                             Just x -> x
                             Nothing -> error "Undefined id."
evalStatCFAE env (If0 c t e) = let (NumV c') = (evalStatCFAE env c)
                               in if c' == 0 then (evalStatCFAE env t) else (evalStatCFAE env e)

interpStatCFAE input = let parseString = (parseCFAE input)
                       in (evalStatCFAE [] parseString)


-- Exercise 3
-- CFBAE AST Definition
data CFBAE where
  NumX :: Int -> CFBAE
  PlusX :: CFBAE -> CFBAE -> CFBAE
  MinusX :: CFBAE -> CFBAE -> CFBAE
  MultX :: CFBAE -> CFBAE -> CFBAE
  DivX :: CFBAE -> CFBAE -> CFBAE
  BindX :: String -> CFBAE -> CFBAE -> CFBAE
  LambdaX :: String -> CFBAE -> CFBAE
  AppX :: CFBAE -> CFBAE -> CFBAE
  IdX :: String -> CFBAE
  If0X :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  IncX :: CFBAE -> CFBAE
  DecX :: CFBAE -> CFBAE
  deriving (Show,Eq)

-- Parser
exprX :: Parser CFBAE
exprX = buildExpressionParser opTableX termX

opTableX = [ [ inFix "*" MultX AssocLeft
            , inFix "/" DivX AssocLeft ]
          , [ inFix "+" PlusX AssocLeft
            , inFix "-" MinusX AssocLeft ]
          ]

numExprX :: Parser CFBAE
numExprX = do i <- integer lexer
              return (NumX (fromInteger i))

identExprX :: Parser CFBAE
identExprX = do i <- identifier lexer
                return (IdX i)

bindExprX :: Parser CFBAE
bindExprX = do reserved lexer "bind"
               i <- identifier lexer
               reservedOp lexer "="
               v <- exprX
               reserved lexer "in"
               e <- exprX
               return (BindX i v e)

lambdaExprX :: Parser CFBAE
lambdaExprX = do reserved lexer "lambda"
                 i <- identifier lexer
                 reserved lexer "in"
                 e <- exprX
                 return (LambdaX i e)

appExprX :: Parser CFBAE
appExprX = do reserved lexer "app"
              e1 <- exprX
              e2 <- exprX
              return (AppX e1 e2)

ifExprX :: Parser CFBAE
ifExprX = do reserved lexer "if0"
             c <- exprX
             reserved lexer "then"
             t <- exprX
             reserved lexer "else"
             e <- exprX
             return (If0X c t e)

incExprX :: Parser CFBAE
incExprX = do reserved lexer "inc"
              x <- exprX
              return (IncX x)

decExprX :: Parser CFBAE
decExprX = do reserved lexer "dec"
              x <- exprX
              return (DecX x)

termX = parens lexer exprX
       <|> numExprX
       <|> identExprX
       <|> bindExprX
       <|> ifExprX
       <|> lambdaExprX
       <|> appExprX
       <|> incExprX
       <|> decExprX

-- Parser invocation
parseCFBAE = parseString exprX

parseCFBAEFile = parseFile exprX

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (NumX x) = (Num x)
elabCFBAE (PlusX l r) = (Plus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (MinusX l r) = (Minus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (MultX l r) = (Mult (elabCFBAE l) (elabCFBAE r))
elabCFBAE (DivX l r) = (Div (elabCFBAE l) (elabCFBAE r))
elabCFBAE (BindX i v b) = (App (Lambda i (elabCFBAE b)) (elabCFBAE v))
elabCFBAE (LambdaX i b) = (Lambda i (elabCFBAE b))
elabCFBAE (AppX f a) = (App (elabCFBAE f) (elabCFBAE a))
elabCFBAE (IdX id) = (Id id)
elabCFBAE (If0X c t e) = (If0 (elabCFBAE c) (elabCFBAE t) (elabCFBAE e))
elabCFBAE (IncX x) = (Plus (elabCFBAE x) (Num 1))
elabCFBAE (DecX x) = (Minus (elabCFBAE x) (Num 1))

evalCFBAE env = evalStatCFAE env . elabCFBAE

interpCFBAE = evalCFBAE [] . parseCFBAE