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


-- AST Pretty Printer

pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ " * " ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ " / " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(isZero " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"


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
                        else Left "Error: Type error mismatch in Plus."
typeof (Minus l r) = let l' = (typeof l)
                         r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TNum)
                        else Left "Error: Type error mismatch in Minus."
typeof (Mult l r) = let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TNum)
                        else Left "Error: Type error mismatch in Mult."
typeof (Div l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then case r of
                                (Num 0) -> (Left "Error: Attempted division by zero.")
                                otherwise -> (Right TNum)
                        else Left "Error: Type error mismatch in Div."
typeof (Boolean b) = (Right TBool)
typeof (IsZero x) = let x' = (typeof x)
                    in if x' == (Right TNum)
                        then (Right TBool)
                        else Left "Error: Type error mismatch in IsZero."
typeof (And l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TBool) && r' == (Right TBool)
                        then (Right TBool)
                        else Left "Error: Type error mismatch in And."
typeof (Leq l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l' == (Right TNum) && r' == (Right TNum)
                        then (Right TBool)
                        else Left "Error: Type error mismatch in Leq."
typeof (If c t e) = let c' = (typeof c)
                        t' = (typeof t)
                        e' = (typeof e)
                    in if c' == (Right TBool) && t' == e'
                        then t'
                        else Left "Error: Type error mismatch in If."


-- Interpreter

interp :: String -> Either String ABE
interp statement =  let e = (parseABE statement) in
                        case (typeof e) of
                            (Left err) -> (Left err)
                            (Right _) -> (eval (optimize e))


-- Code optimizer which replaces a few cases of silly statements such as "x + 0" or if true...

optimize :: ABE -> ABE
optimize (Num x) = (Num x)
optimize (Plus l r) = let l' = (optimize l)
                          r' = (optimize r)
                      in if l' == (Num 0)
                         then r'
                         else if r' == (Num 0)
                              then l'
                              else (Plus l' r')
-- Do nothing if the left argument is 0 as subtraction still occurs (relative to right operand)
optimize (Minus l r) = let l' = (optimize l)
                           r' = (optimize r)
                       in if r' == (Num 0)
                          then l'
                          else (Minus l' r')
optimize (Mult l r) = let l' = (optimize l)
                          r' = (optimize r)
                      in if l' == (Num 0)
                          then (Num 0)
                          else if r' == (Num 0)
                               then (Num 0)
                               else (Mult l' r')
optimize (Div l r) = if l == (Num 0)
                     then (Num 0)
                     else (Div (optimize l) (optimize r))
optimize (Boolean x) = (Boolean x)
-- Do I need this definition?
optimize (IsZero x) = (IsZero (optimize x))
optimize (And l r) = if (optimize r) == (Boolean False)
                     then (Boolean False)
                     else (if (optimize l) == (Boolean False)
                           then (Boolean False)
                           else (And (optimize l) (optimize r)))
optimize (Leq l r) = (Leq (optimize l) (optimize r))
optimize (If c t e) = let c' = (optimize c)
                          t' = (optimize t)
                          e' = (optimize e)
                      in case c' of
                            (Boolean True) -> t'
                            (Boolean False) -> e'
                            (_) -> (If c t' e')


-- Arbitrary AST Generator

instance Arbitrary ABE where
  arbitrary =
    sized $ \n -> genABE (rem n 10)

genNum =
  do t <- choose (0,100)
     return (Num t)

genBool =
  do t <- choose (True,False)
     return (Boolean t)

genPlus n =
  do s <- genABE n
     t <- genABE n
     return (Plus s t)

genMinus n =
  do s <- genABE n
     t <- genABE n
     return (Minus s t)

genMult n =
  do s <- genABE n
     t <- genABE n
     return (Mult s t)

genDiv n =
  do s <- genABE n
     t <- genABE n
     return (Div s t)

genAnd n =
  do s <- genABE n
     t <- genABE n
     return (And s t)

genLeq n =
  do s <- genABE n
     t <- genABE n
     return (Leq s t)

genIsZero n =
  do s <- genABE n
     return (IsZero s)

genIf n =
  do s <- genABE n
     t <- genABE n
     u <- genABE n
     return (If s t u)

genABE :: Int -> Gen ABE
genABE 0 = 
  do term <- oneof [genNum,genBool]
     return term
genABE n =
  do term <- oneof [genNum,(genPlus (n-1))
                   ,(genMinus (n-1))
                   ,(genMult (n-1))
                   ,(genDiv (n-1))
                   ,(genAnd (n-1))
                   ,(genLeq (n-1))
                   ,(genIsZero (n-1))
                   ,(genIf (n-1))]
     return term

-- QuickCheck 

testTypeof :: Int -> IO ()
testTypeof n = quickCheckWith stdArgs {maxSuccess=n}
  (\t-> case typeof t of
      (Right _) -> True
      (Left _) -> True)

testTypedEval :: Int -> IO ()
testTypedEval n =
  quickCheckWith stdArgs {maxSuccess=n}
  (\t -> case typeof t of
           (Right _) -> eval (parseABE (pprint t)) == (eval t)
           (Left _) -> True)

eqInterp :: Either String ABE -> Either String ABE -> Bool
eqInterp s t =
  case s of
    (Right x) -> case t of
                  (Right y) -> x == y
                  (Left _) -> False
    (Left x) -> case t of
                   (Right y) -> False
                   (Left _) -> True