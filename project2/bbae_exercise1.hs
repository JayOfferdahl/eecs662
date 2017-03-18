{-# LANGUAGE GADTs #-}

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

-- Imports for PLIH
import ParserUtils

-- Imports for UnsafePerformIO
import System.IO.Unsafe
--
-- Simple caculator with variables extended Booleans and both static and
-- dynamic type checking.
--
-- Author: Perry Alexander
-- Date: Wed Jul 13 11:24:46 CDT 2016
--
-- Source files for the Boolean Binding Arithmetic Expressions (BBAE)
-- language from PLIH
--
-- Edited by: Jay Offerdahl
-- Date: Fri Mar 17 1:13:43 CDT 2017

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  Seq :: BBAE -> BBAE -> BBAE
  Print :: BBAE -> BBAE
  deriving (Show,Eq)

-- Ast Pretty Printer

pprint :: BBAE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(isZero " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"
pprint (Id s) = s
pprint (Bind n v b) = "(bind " ++ n ++ " = " ++ pprint v ++ " in " ++ pprint b ++ ")"

-- Parser
expr :: Parser BBAE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "+" Plus AssocLeft
              , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser BBAE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

identExpr :: Parser BBAE
identExpr = do i <- identifier lexer
               return (Id i)

bindExpr :: Parser BBAE
bindExpr = do reserved lexer "bind"
              i <- identifier lexer
              reservedOp lexer "="
              v <- expr
              reserved lexer "in"
              e <- expr
              return (Bind i v e)

trueExpr :: Parser BBAE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser BBAE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser BBAE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

seqExpr :: Parser BBAE
seqExpr = do reserved lexer "seq"
             f <- expr
             s <- expr
             return (Seq f s)

printExpr :: Parser BBAE
printExpr = do reserved lexer "print"
               t <- expr
               return (Print t)
             
term = parens lexer expr
       <|> numExpr
       <|> identExpr
       <|> bindExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr
       <|> printExpr
       <|> seqExpr

parseBAE = parseString expr

parseBAEFile = parseFile expr

-- Parser invocation

parseBBAE = parseString expr

parseBBAEFile = parseFile expr

type Env = [(String,BBAE)]
    
eval :: Env -> BBAE -> (Either String BBAE)
eval env (Num x) = (Right (Num x))
eval env (Plus l r) =
  case (eval env l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (eval env r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Num (v1 + v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Plus.")
    (Right _) -> (Left "Error: Type error mismatch in Plus.")
eval env (Minus l r) =
  case (eval env l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (eval env r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Num (v1 - v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Minus.")
    (Right _) -> (Left "Error: Type error mismatch in Minus.")
eval env (Bind i v b) = let v' = eval env v in
                        case v' of
                          (Left e) -> (Left e)
                          (Right y) -> (eval ((i,y):env) b)
eval env (Id id) = case (lookup id env) of
                     Just x -> (Right x)
                     Nothing -> (Left "Varible not found")
eval env (Boolean x) = (Right (Boolean x))
eval env (IsZero x) =
  case (eval env x) of
    (Left e) -> (Left e)
    (Right (Num y)) -> (Right (Boolean (y == 0)))
    (Right _) -> (Left "Error: Type error mismatch in IsZero.")
eval env (And l r) =
  case (eval env l) of
    (Left e) -> (Left e)
    (Right (Boolean v1)) -> case (eval env r) of
                              (Left e) -> (Left e)
                              (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                              (Right _) -> (Left "Error: Type error mismatch in And.")
    (Right _) -> (Left "Error: Type error mismatch in And.")
eval env (Leq l r) =
  case (eval env l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (eval env r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Boolean (v1 <= v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Leq.")
    (Right _) -> (Left "Error: Type error mismatch in Leq.")
eval env (If c t e) =
  case (eval env c) of
    (Left e) -> (Left e)
    (Right (Boolean v1)) -> case v1 of
                              (True) -> (eval env t)
                              (False) -> (eval env e)
    (Right _) -> (Left "Error: Type error mismatch in If.")
eval env (Seq x y) = 
  case x of
    (Print t) -> unsafePerformIO $ print (Print t) >> return (eval env y)
    _ ->  
      do x' <- (eval env x)
         y' <- (eval env y)
         return y'
eval env (Print x) =
  do x' <- (eval env x)
     return (Num 0)

-- subst for evals
subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if i==i'
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i'
                    then v
                    else (Id i')
subst _ _ (Boolean x) = (Boolean x)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero t) = (IsZero (subst i v t))
subst i v (If t1 t2 t3) = (If (subst i v t1) (subst i v t2) (subst i v t3))

-- Exercise 1: evals (eval using subst)
evals :: BBAE -> (Either String BBAE)
evals (Num x) = (Right (Num x))
evals (Plus l r) =
  case (evals l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (evals r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Num (v1 + v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Plus.")
    (Right _) -> (Left "Error: Type error mismatch in Plus.")
evals (Minus l r) =
  case (evals l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (evals r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Num (v1 - v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Minus.")
    (Right _) -> (Left "Error: Type error mismatch in Minus.")
evals (Bind i v b) = let x = evals v
                     in case x of
                          (Left e) -> (Left e)
                          (Right y) -> (evals (subst i y b))
-- If an id is accessed, it's not declared (Wasn't substituted)
evals (Id id) = (Left "Undeclared variable.")
evals (Boolean x) = (Right (Boolean x))
evals (IsZero x) =
  case (evals x) of
    (Left e) -> (Left e)
    (Right (Num y)) -> (Right (Boolean (y == 0)))
    (Right _) -> (Left "Error: Type error mismatch in IsZero.")
evals (And l r) =
  case (evals l) of
    (Left e) -> (Left e)
    (Right (Boolean v1)) -> case (evals r) of
                              (Left e) -> (Left e)
                              (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                              (Right _) -> (Left "Error: Type error mismatch in And.")
    (Right _) -> (Left "Error: Type error mismatch in And.")
evals (Leq l r) =
  case (evals l) of
    (Left e) -> (Left e)
    (Right (Num v1)) -> case (evals r) of
                          (Left e) -> (Left e)
                          (Right (Num v2)) -> (Right (Boolean (v1 <= v2)))
                          (Right _) -> (Left "Error: Type error mismatch in Leq.")
    (Right _) -> (Left "Error: Type error mismatch in Leq.")
evals (If c t e) =
  case (evals c) of
    (Left e) -> (Left e)
    (Right (Boolean v1)) -> case v1 of
                              (True) -> (evals t)
                              (False) -> (evals e)
    (Right _) -> (Left "Error: Type error mismatch in If.")
evals (Seq x y) = 
  case x of
    (Print t) -> unsafePerformIO $ print (Print t) >> return (evals y)
    _ ->  
      do x' <- (evals x)
         y' <- (evals y)
         return y'
evals (Print x) =
  do x' <- (evals x)
     return (Num 0)

interp = (eval []) . parseBBAE
interps = evals . parseBBAE
