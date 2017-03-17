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
-- Source files for the Boolean Binding Arithmetic Expressions (BBAEL)
-- language from PLIH
--
-- Edited by: Jay Offerdahl
-- Date: Fri Mar 17 1:13:43 CDT 2017

data BBAEL where
  Num :: Int -> BBAEL
  Plus :: BBAEL -> BBAEL -> BBAEL
  Minus :: BBAEL -> BBAEL -> BBAEL
  Bind :: String -> BBAEL -> BBAEL -> BBAEL
  Id :: String -> BBAEL
  Boolean :: Bool -> BBAEL
  And :: BBAEL -> BBAEL -> BBAEL
  Leq :: BBAEL -> BBAEL -> BBAEL
  IsZero :: BBAEL -> BBAEL
  If :: BBAEL -> BBAEL -> BBAEL -> BBAEL
  Seq :: BBAEL -> BBAEL -> BBAEL
  Print :: BBAEL -> BBAEL
  First :: BBAEL -> BBAEL
  Rest :: BBAEL -> BBAEL
  Cons :: BBAEL -> BBAEL -> BBAEL
  Empty :: BBAEL
  IsEmpty :: BBAEL -> BBAEL
  deriving (Show,Eq)

-- Ast Pretty Printer

pprint :: BBAEL -> String
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
expr :: Parser BBAEL
expr = buildExpressionParser opTable term

opTable = [ [ inFix "+" Plus AssocLeft
              , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser BBAEL
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

identExpr :: Parser BBAEL
identExpr = do i <- identifier lexer
               return (Id i)

bindExpr :: Parser BBAEL
bindExpr = do reserved lexer "bind"
              i <- identifier lexer
              reservedOp lexer "="
              v <- expr
              reserved lexer "in"
              e <- expr
              return (Bind i v e)

trueExpr :: Parser BBAEL
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser BBAEL
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser BBAEL
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

seqExpr :: Parser BBAEL
seqExpr = do reserved lexer "seq"
             f <- expr
             s <- expr
             return (Seq f s)

printExpr :: Parser BBAEL
printExpr = do reserved lexer "print"
               t <- expr
               return (Print t)

consExpr :: Parser BBAEL
consExpr = do reserved lexer "cons"
              f <- expr
              s <- expr
              return (Cons f s)

firstExpr :: Parser BBAEL
firstExpr = do reserved lexer "first"
               t <- expr
               return (First t)
             
restExpr :: Parser BBAEL
restExpr = do reserved lexer "rest"
              t <- expr
              return (Rest t)

isEmptyExpr :: Parser BBAEL
isEmptyExpr = do reserved lexer "isEmpty"
                 t <- expr
                 return (IsEmpty t)

emptyExpr :: Parser BBAEL
emptyExpr = do reserved lexer "empty"
               return Empty
             
term = parens lexer expr
       <|> numExpr
       <|> identExpr
       <|> bindExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr
       <|> consExpr
       <|> firstExpr
       <|> restExpr              
       <|> isEmptyExpr
       <|> emptyExpr
       <|> printExpr
       <|> seqExpr

parseBAE = parseString expr

parseBAEFile = parseFile expr

-- Parser invocation

parseBBAEL = parseString expr

parseBBAELFile = parseFile expr

type Env = [(String,BBAEL)]
    
eval :: Env -> BBAEL -> (Either String BBAEL)
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
     return x'
eval env (Cons f s) = 
  do x <- (eval env f)
     y <- (eval env s)
     return (Cons x y)
eval env (First t) = let (Right x) = (eval env t) in
                     case x of
                       (Cons t1 t2) -> (Right t1)
                       _ -> (Left "Not a list")
eval env (Rest t) = let (Right r) = (eval env t) in
                    case r of
                      (Cons t1 t2) -> (Right t2)
                      _ -> (Left "Not a list")
eval env (IsEmpty t) = let (Right r) = (eval env t) in
                       case r of
                         Empty -> (Right (Boolean True))
                         _ -> (Right (Boolean False))
eval env (Empty) = (Right Empty)      

interp = (eval []) . parseBBAEL
