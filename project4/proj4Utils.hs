{-# LANGUAGE GADTs, FlexibleContexts #-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token

--
-- Project utilities for developing the FBAE interpreter.
--
-- Edited By: Jay Offerdahl
-- Date: 08 May 2017
--

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

tokenDef =
  javaStyle { Token.identStart = letter
            , Token.identLetter = alphaNum
            , Token.reservedNames = [ "lambda"
                                    , "bind"
                                    , "in"
                                    , "if"
                                    , "then"
                                    , "else"
                                    , "isZero"
                                    , "app"
                                    , "Num"
                                    , "Bool"
                                    , "true"
                                    , "false"
                                    , "fix" ]
            , Token.reservedOpNames = [ "+","-","*","/","&&","||","<=","=",":","->"]
            }

lexer = Token.makeTokenParser tokenDef

identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
integer = Token.integer lexer
whiteSpace = Token.whiteSpace lexer

-- Term parser

expr :: Parser FBAE
expr = buildExpressionParser operators term

operators = [ [Infix (reservedOp "*" >> return (Mult )) AssocLeft,
               Infix (reservedOp "/" >> return (Div )) AssocLeft ]
            , [Infix (reservedOp "+" >> return (Plus )) AssocLeft,
               Infix (reservedOp "-" >> return (Minus )) AssocLeft ]
            , [Infix (reservedOp "&&" >> return (And )) AssocLeft,
               Infix (reservedOp "||" >> return (Or )) AssocLeft]
            , [Infix (reservedOp "<=" >> return (Leq )) AssocLeft ]
            , [Prefix (reserved "isZero" >> return (IsZero )) ]
            ]

numExpr :: Parser FBAE
numExpr = do i <- integer
             return (Num (fromInteger i))

trueExpr :: Parser FBAE
trueExpr = do i <- reserved "true"
              return (Boolean True)

falseExpr :: Parser FBAE
falseExpr = do i <- reserved "false"
               return (Boolean False)

ifExpr :: Parser FBAE
ifExpr = do reserved "if"
            c <- expr
            reserved "then"
            t <- expr
            reserved "else"
            e <- expr
            return (If c t e)

identExpr :: Parser FBAE
identExpr = do i <- identifier
               return (Id i)

bindExpr :: Parser FBAE
bindExpr = do reserved "bind"
              i <- identifier
              reservedOp "="
              v <- expr
              reserved "in"
              e <- expr
              return (Bind i v e)

lambdaExpr :: Parser FBAE
lambdaExpr = do reserved "lambda"
                (i,t) <- parens argExpr
                reserved "in"
                b <- expr
                return (Lambda i t b)

argExpr :: Parser (String,TFBAE)
argExpr = do i <- identifier
             reservedOp ":"
             t <- ty
             return (i,t)

appExpr :: Parser FBAE
appExpr = do reserved "app"
             f <- expr
             a <- expr
             return (App f a)

fixExpr :: Parser FBAE
fixExpr = do reserved "fix"
             t <- expr
             return (Fix t)

term = parens expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr
       <|> identExpr
       <|> bindExpr
       <|> lambdaExpr
       <|> appExpr
       <|> fixExpr

-- Type parser

ty = buildExpressionParser tyoperators tyTerm

tyoperators = [ [Infix (reservedOp "->" >> return (:->: )) AssocLeft ] ]

tyTerm :: Parser TFBAE
tyTerm = parens ty <|> tyNat <|> tyBool

tyNat :: Parser TFBAE
tyNat = do reserved "Nat"
           return TNum

tyBool :: Parser TFBAE
tyBool = do reserved "Bool"
            return TBool

-- Parser invocation

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

parseFBAE = parseString expr

parseFile p file =
  do program <- readFile file
     case parse p "" program of
       Left e -> print e >> fail "parse error"
       Right r -> return r

parseFBAEFile = parseFile expr


-- Exercise 1
type EnvS = [(String, FBAEVal)]

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> FBAE -> EnvS -> FBAEVal
  deriving (Show,Eq)

evalFBAE :: EnvS -> FBAE -> FBAEVal
evalFBAE env (Num x) = (NumV x)
evalFBAE env (Plus l r) = let (NumV l') = (evalFBAE env l)
                              (NumV r') = (evalFBAE env r)
                              in (NumV (l' + r'))
evalFBAE env (Minus l r) = let (NumV l') = (evalFBAE env l)
                               (NumV r') = (evalFBAE env r)
                               in (NumV (l' - r'))
evalFBAE env (Mult l r) = let (NumV l') = (evalFBAE env l)
                              (NumV r') = (evalFBAE env r)
                              in (NumV (l' * r'))
evalFBAE env (Div l r) = let (NumV l') = (evalFBAE env l)
                             (NumV r') = (evalFBAE env r)
                             in case r' of 
                                  0 -> error "Attempted division by 0."
                                  _ -> (NumV (div l' r'))
evalFBAE env (Bind i v b) = evalFBAE env (App (Lambda i TNum b) v)
evalFBAE env (Lambda i t b) = (ClosureV i b env)
evalFBAE env (App f a) =  let (ClosureV i b e) = (evalFBAE env f)
                              a' = (evalFBAE env a)
                              in evalFBAE ((i, a'):e) b
evalFBAE env (Id id) = case (lookup id env) of
                         Just x -> x
                         Nothing -> error "Undefined id."
evalFBAE env (Boolean i) = (BooleanV i)
evalFBAE env (And l r) = let (BooleanV l') = (evalFBAE env l)
                             (BooleanV r') = (evalFBAE env r)
                             in (BooleanV (l' && r'))
evalFBAE env (Or l r) = let (BooleanV l') = (evalFBAE env l)
                            (BooleanV r') = (evalFBAE env r)
                            in (BooleanV (l' || r'))
evalFBAE env (Leq l r) = let (BooleanV l') = (evalFBAE env l)
                             (BooleanV r') = (evalFBAE env r)
                             in (BooleanV (l' <= r'))
evalFBAE env (IsZero i) = let (NumV i') = (evalFBAE env i)
                              in (BooleanV (i' == 0))
evalFBAE env (If c t e) = let (BooleanV c') = (evalFBAE env c)
                              in if c' then (evalFBAE env t) else (evalFBAE env e)
evalFBAE env (Fix f) = let (ClosureV i b e) = (evalFBAE env f)
                           in evalFBAE ((i, (evalFBAE e (Fix (Lambda i TNum b)))):e) b

interp input = let parseString = (parseFBAE input)
                   in (evalFBAE [] parseString)


-- Exercise 3
type Cont = [(String, TFBAE)]

typeof :: Cont -> FBAE -> TFBAE
typeof cont (Num x) = TNum
typeof cont (Plus l r) = let l' = (typeof cont l)
                             r' = (typeof cont r)
                             in if l' == TNum && r' == TNum
                                then TNum
                                else error "Error: Type error mismatch in Plus."
typeof cont (Minus l r) = let l' = (typeof cont l)
                              r' = (typeof cont r)
                              in if l' == TNum && r' == TNum
                                 then TNum
                                 else error "Error: Type error mismatch in Minus."
typeof cont (Mult l r) = let l' = (typeof cont l)
                             r' = (typeof cont r)
                             in if l' == TNum && r' == TNum
                                then TNum
                                else error "Error: Type error mismatch in Mult."
typeof cont (Div l r) = let l' = (typeof cont l)
                            r' = (typeof cont r)
                            in if l' == TNum && r' == TNum
                               then TNum
                               else error "Error: Type error mismatch in Div."
typeof cont (Bind i v b) = let v' = (typeof cont v)
                               in (typeof ((i,v'):cont) b)
typeof cont (Lambda x d b) = let r = (typeof ((x,d):cont) b)
                                 in d :->: r
typeof cont (App x y) = let ty = (typeof cont y)
                            in case (typeof cont x) of
                                 txd :->: txr -> if txd == ty
                                                 then txr
                                                 else error "Error: Type error mismatch in App."
                                 _ -> error "Error: App expects first argument to be a function (lambda)."
typeof cont (Id id) = case (lookup id cont) of
                        Just x -> x
                        Nothing -> error "Error:Undefined id."
typeof cont (Boolean b) = TBool
typeof cont (And l r) = let l' = (typeof cont l)
                            r' = (typeof cont r)
                            in if l' == TBool && r' == TBool
                               then TBool
                               else error "Error: Type error mismatch in And."
typeof cont (Or l r) = let l' = (typeof cont l)
                           r' = (typeof cont r)
                           in if l' == TBool && r' == TBool
                              then TBool
                              else error "Error: Type error mismatch in Or."
typeof cont (Leq l r) = let l' = (typeof cont l)
                            r' = (typeof cont r)
                            in if l' == TNum && r' == TNum
                               then TBool
                               else error "Error: Type error mismatch in Leq."
typeof cont (IsZero x) = let x' = (typeof cont x)
                             in if x' == TNum
                                then TBool
                                else error "Error: Type error mismatch in IsZero."
typeof cont (If c t e) = let c' = (typeof cont c)
                             t' = (typeof cont t)
                             e' = (typeof cont e)
                             in if c' == TBool && t' == e'
                                then t'
                                else error "Error: Type error mismatch in If."
typeof cont (Fix f) = case f of
                        (Lambda i t b) -> case (typeof cont f) of
                                            d :->: r -> (typeof ((i, d):cont) b)
                        _ -> error "Error: Type error mismatch in Fix (no function given)."

interpTyped input = let parseString = (parseFBAE input)
                        in case typeof [] parseString of
                             TNum -> evalFBAE [] parseString
                             TBool -> evalFBAE [] parseString
                             d :->: r -> evalFBAE [] parseString
