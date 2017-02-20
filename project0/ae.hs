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

--
-- Simple caculator over naturals with no identifiers
--
-- Author: Perry Alexander
-- Date: Mon Jun 27 13:34:57 CDT 2016
--
-- Source files for the Arithmetic Expressions Extended (AEE) language from PLIH
--
-- Edited by: Jay Offerdahl
-- Date: Thu Feb 09 18:00:15 CDT 2016
-- 
-- Added multiply and division capabilties as well as a simple conditional check

-- AST Definition

data AEE where
  Num :: Int -> AEE
  Plus :: AEE -> AEE -> AEE
  Minus :: AEE -> AEE -> AEE
  Mult :: AEE -> AEE -> AEE
  Div :: AEE -> AEE -> AEE
  If0 :: AEE -> AEE -> AEE -> AEE
  deriving (Show,Eq)

-- AST Pretty Printer

pprint :: AEE -> String
pprint (Num n) = show n
pprint (Plus n m) = "(" ++ pprint n ++ "+" ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ "-" ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ "*" ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ "/" ++ pprint m ++ ")"
pprint (If0 c n m) = "(if0 " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"

--instance Show AEE where
--  show = pprint

-- Parser (Requires ParserUtils and Parsec)

expr :: Parser AEE
expr = buildExpressionParser operators term

operators = [ [ inFix "*" Mult AssocLeft
              , inFix "/" Div AssocLeft ]
              ,
              [ inFix "+" Plus AssocLeft
              , inFix "-" Minus AssocLeft ]
            ]

numExpr :: Parser AEE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

if0Expr :: Parser AEE
if0Expr =  do reserved lexer "if0"
              c <- expr
              reserved lexer "then"
              n <- expr
              reserved lexer "else"
              m <- expr
              return (If0 c n m)

term = parens lexer expr
       <|> numExpr
       <|> if0Expr

-- Parser invocation

parseAEE = parseString expr

parseAEEFile = parseFile expr

-- Evaluation Function

eval :: AEE -> AEE
eval (Num x) = (Num x)
eval (Plus t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1+v2))
eval (Minus t1 t2) = let (Num v1) = (eval t1)
                         (Num v2) = (eval t2)
                     in (Num (v1-v2))
eval (Mult t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1*v2))
eval (Div t1 t2) = let (Num v1) = (eval t1)
                       (Num v2) = (eval t2)
                   in (Num (div v1 v2))
eval (If0 t1 t2 t3) = let (Num v1) = (eval t1)
                      in if (v1 == 0) then (eval t2) else (eval t3)

-- Interpreter = parse + eval

interp = eval . parseAEE

-- Testing (Requires QuickCheck 2)

-- Arbitrary AST Generator

instance Arbitrary AEE where
  arbitrary =
    sized $ \n -> genAEE ((rem n 10) + 10)

genNum =
  do t <- choose (0,100)
     return (Num t)

genPlus n =
  do s <- genAEE n
     t <- genAEE n
     return (Plus s t)

genMinus n =
  do s <- genAEE n
     t <- genAEE n
     return (Minus s t)

genMult n =
  do s <- genAEE n
     t <- genAEE n
     return (Mult s t)

genDiv n =
  do s <- genAEE n
     t <- genAEE n
     return (Div s t)

genIf0 n =
  do c <- genAEE n
     t <- genAEE n
     e <- genAEE n
     return (If0 c t e)

genAEE :: Int -> Gen AEE
genAEE 0 =
  do term <- genNum
     return term
genAEE n =
  do term <- oneof [genNum,
                    (genPlus (n-1)),
                    (genMinus (n-1)),
                    (genMult (n-1)),
                    (genDiv (n-1)),
                    (genIf0 (n-1))
                    ]
     return term

-- QuickCheck 

testParser :: Int -> IO ()
testParser n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> parseAEE (pprint t) == t)

testEval' :: Int -> IO ()
testEval' n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> (interp $ pprint t) == (eval t))
