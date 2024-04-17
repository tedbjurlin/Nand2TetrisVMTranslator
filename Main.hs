{-# LANGUAGE GADTs #-}
module Main where

import           Data.Void (Void)
import           Text.Megaparsec as P (Parsec, empty, try, (<|>), eof, many, parse, errorBundlePretty, choice)
import           Text.Megaparsec.Char (string, space1, letterChar, char, digitChar)
import qualified Text.Megaparsec.Char.Lexer as L
import           System.Environment (getArgs)
import           System.FilePath.Posix (takeBaseName, (</>), (-<.>), (<.>), takeDirectory)
import           System.Directory (listDirectory, doesFileExist)

data Command where
    Push       :: Segment -> Integer -> Command
    Pop        :: Segment -> Integer -> Command
    ArithLogic :: Operation -> Command
    Label      :: String -> Command
    Goto       :: String -> Command
    IfGoto     :: String -> Command
    Function   :: String -> Integer -> Command
    Call       :: String -> Integer -> Command
    Return     :: Command
    deriving (Show, Eq)

type Prog = [ Command ]

data Segment = Argument | Local | Static | Constant | This | That | Pointer | Temp
    deriving (Show, Eq)

data Operation = Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not
    deriving (Show, Eq)

type Parser = Parsec Void String

whitespace :: Parser ()
whitespace = L.space
  space1
  (L.skipLineComment "//")
  P.empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme whitespace

reserved :: String -> Parser String
reserved = lexeme . P.try . string

integer :: Parser Integer
integer = lexeme L.decimal

pPush :: Parser Command
pPush = Push <$> (reserved "push" *> pSegment) <*> integer

pPop :: Parser Command
pPop = Pop <$> (reserved "pop" *> pSegment) <*> integer

pSegment :: Parser Segment
pSegment
    =   Argument <$ reserved "argument"
    <|> Local    <$ reserved "local"
    <|> Static   <$ reserved "static"
    <|> Constant <$ reserved "constant"
    <|> This     <$ reserved "this"
    <|> That     <$ reserved "that"
    <|> Pointer  <$ reserved "pointer"
    <|> Temp     <$ reserved "temp"

pArithLogic :: Parser Command
pArithLogic
    =   ArithLogic Add <$ reserved "add"
    <|> ArithLogic Sub <$ reserved "sub"
    <|> ArithLogic Neg <$ reserved "neg"
    <|> ArithLogic Eq <$ reserved "eq"
    <|> ArithLogic Gt <$ reserved "gt"
    <|> ArithLogic Lt <$ reserved "lt"
    <|> ArithLogic And <$ reserved "and"
    <|> ArithLogic Or <$ reserved "or"
    <|> ArithLogic Not <$ reserved "not"

partSymbol :: Parser String
partSymbol = do
  a <- choice
    [ letterChar
    , char '_'
    , char '.'
    , char ':' ]
  rest <-  many $ choice
    [ letterChar
    , digitChar
    , char '_'
    , char '.'
    , char ':' ]
  return $ a:rest

pLabel :: Parser Command
pLabel = Label <$> (reserved "label" *> lexeme partSymbol)

pGoto :: Parser Command
pGoto = Goto <$> (reserved "goto" *> lexeme partSymbol)

pIfGoto :: Parser Command
pIfGoto = IfGoto <$> (reserved "if-goto" *> lexeme partSymbol)

pFunction :: Parser Command
pFunction = Function <$> (reserved "function" *> lexeme partSymbol) <*> integer

pCall :: Parser Command
pCall = Call <$> (reserved "call" *> lexeme partSymbol) <*> integer

pReturn :: Parser Command
pReturn = Return <$ reserved "return"

pCommand :: Parser Command
pCommand
    =   P.try pPush
    <|> P.try pPop
    <|> P.try pArithLogic
    <|> P.try pLabel
    <|> P.try pGoto
    <|> P.try pIfGoto
    <|> P.try pFunction
    <|> P.try pCall
    <|> pReturn

pProg :: Parser Prog
pProg = whitespace *> many pCommand <* eof

translate :: Integer -> String -> String -> Prog -> String
translate _ _ _ []       = ""
translate idx fn fun (p:ps) = case p of
    Push seg i       -> tPush fn seg i ++ translate idx fn fun ps
    Pop seg i        -> tPop fn seg i ++ translate idx fn fun ps
    ArithLogic op    -> tOperation idx op fn fun ps
    Label l          -> tLabel fun l ++ translate idx fn fun ps
    Goto l           -> tGoto fun l ++ translate idx fn fun ps
    IfGoto l         -> tIfGoto fun l ++ translate idx fn fun ps
    Call f nArgs     -> tCall idx f nArgs ++ translate (idx+1) fn fun ps
    Function f nVars -> tFunction f nVars ++ translate idx fn f ps
    Return           -> tReturn ++ translate idx fn fun ps


tOperation :: Integer -> Operation -> String -> String -> Prog -> String
tOperation idx op fn fun p = case op of
    Add -> tBinary ++ "M=D+M\n" ++ translate idx fn fun p
    Sub -> tBinary ++ "M=M-D\n" ++ translate idx fn fun p
    Neg -> tUnary  ++ "M=-M\n" ++ translate idx fn fun p
    Eq  -> tBinary ++ "D=M-D\n@"++fun++"$EQUIV$TRUE."++show idx
        ++"\nD;JEQ\n@SP\nA=M-1\nM=0\n@"++fun++"$EQUIV$END."++show idx++"\n0;JMP\n("++fun++"$EQUIV$TRUE."
        ++show idx++")\n@SP\nA=M-1\nM=-1\n("++fun++"$EQUIV$END."++show idx++")\n" ++ translate (idx+1) fn fun p
    Gt  -> tBinary ++ "D=M-D\n@"++fun++"$GREATER$TRUE."++show idx
        ++"\nD;JGT\n@SP\nA=M-1\nM=0\n@"++fun++"$GREATER$END."++show idx++"\n0;JMP\n("++fun++"$GREATER$TRUE."
        ++show idx++")\n@SP\nA=M-1\nM=-1\n("++fun++"$GREATER$END."++show idx++")\n" ++ translate (idx+1) fn fun p
    Lt  -> tBinary ++ "D=M-D\n@"++fun++"$LESSER$TRUE."++show idx
        ++"\nD;JLT\n@SP\nA=M-1\nM=0\n@"++fun++"$LESSER$END."++show idx++"\n0;JMP\n("++fun++"$LESSER$TRUE."
        ++show idx++")\n@SP\nA=M-1\nM=-1\n("++fun++"$LESSER$END."++show idx++")\n" ++ translate (idx+1) fn fun p
    And -> tBinary ++ "M=D&M\n" ++ translate idx fn fun p
    Or  -> tBinary ++ "M=D|M\n" ++ translate idx fn fun p
    Not -> tUnary  ++ "M=!M\n" ++ translate idx fn fun p

tUnary :: String
tUnary = "@SP\nA=M-1\n"

tBinary :: String
tBinary = "@SP\nM=M-1\nA=M\nD=M\n@SP\nA=M-1\n"

tPush :: String -> Segment -> Integer -> String
tPush fn Constant i = lookupSegmentAddress fn Constant i ++ "D=A\n"++push
tPush fn s i        = lookupSegmentAddress fn s i ++ "D=M\n"++push

tPop :: String -> Segment -> Integer -> String
tPop fn s i = lookupSegmentAddress fn s i
    ++ "D=A\n@R13\nM=D\n@SP\nM=M-1\nA=M\nD=M\n@R13\nA=M\nM=D\n"

lookupSegmentAddress :: String -> Segment -> Integer -> String
lookupSegmentAddress _ Constant i = '@':show i++"\n"
lookupSegmentAddress _ Temp i     = '@':show (i + 5)++"\n"
lookupSegmentAddress fileName Static i = '@':fileName++"."++show i++"\n"
lookupSegmentAddress _ Pointer i  = '@':show (3 + i)++"\n"
lookupSegmentAddress _ This i     = mutSeg 3 i
lookupSegmentAddress _ That i     = mutSeg 4 i
lookupSegmentAddress _ Argument i = mutSeg 2 i
lookupSegmentAddress _ Local i    = mutSeg 1 i

mutSeg :: Integer -> Integer -> String
mutSeg n i = ('@':show n)++"\nD=M\n"++('@':show i)++"\nA=D+A\n"

tLabel :: String -> String -> String
tLabel fun l = '(':fun++"$"++l++")\n"

tGoto :: String -> String -> String
tGoto fun l = '@':fun++"$"++l++"\n0;JMP\n"

tIfGoto :: String -> String -> String
tIfGoto fun l = "@SP\nM=M-1\nA=M\nD=M\n@"++fun++"$"++l++"\nD;JNE\n"

tCall :: Integer -> String -> Integer -> String
tCall idx f nArgs = '@':f++"$ret."++show idx
  ++"\nD=A\n"++push++"@LCL\nD=M\n"++push++"@ARG\nD=M\n"++push
  ++"@THIS\nD=M\n"++push++"@THAT\nD=M\n"++push
  ++"@SP\nD=M\n@5\nD=D-A\n@"++show nArgs++"\nD=D-A\n@ARG\nM=D\n@SP\nD=M\n@LCL\nM=D\n@"
  ++ f ++ "\n0;JMP\n("++f++"$ret."++show idx++")\n"

tFunction :: String -> Integer -> String
tFunction f nVars = "("++f++")\n"++concat (replicate (fromIntegral nVars) push0)

tReturn :: String
tReturn = "@LCL\nD=M\n@frame\nM=D\n@5\nA=D-A\nD=M\n@retAddr\nM=D\n@SP\nM=M-1\nA=M\nD=M\n\
  \@ARG\nA=M\nM=D\n@ARG\nD=M\nD=D+1\n@SP\nM=D\n@frame\nA=M-1\nD=M\n@THAT\nM=D\n\
  \@frame\nD=M\n@2\nA=D-A\nD=M\n@THIS\nM=D\n@frame\nD=M\n@3\nA=D-A\nD=M\n@ARG\nM=D\n\
  \@frame\nD=M\n@4\nA=D-A\nD=M\n@LCL\nM=D\n@retAddr\nA=M\n0;JMP\n"

push0 :: String
push0 = "D=0\n@SP\nA=M\nM=D\n@SP\nM=M+1\n"

push :: String
push = "@SP\nA=M\nM=D\n@SP\nM=M+1\n"

bootstrap :: String
bootstrap = "@256\nD=A\n@SP\nM=D\n" ++ tCall 0 "Sys.init" 0

parseProg :: String -> Prog
parseProg s = case parse pProg "" s of
  Left err -> error (errorBundlePretty err)
  Right p  -> p

process :: String -> String -> String
process filepath contents =
  let (program, filename) = (parseProg contents, takeBaseName filepath)
    in translate 0 filename "" program

processIO :: String -> IO String
processIO filepath = do
  contents <- readFile filepath
  let (program, filename) = (parseProg contents, takeBaseName filepath)
  return $ translate 0 filename "" program

processFromPath :: String -> IO String
processFromPath filepath = do
  con <- doesFileExist filepath
  if con
    then do
      contents <- readFile filepath
      return $ process filepath contents
    else do
      files <- listDirectory filepath
      progs <- mapM processIO (filter isVM (map (filepath </>) files))
      return $ bootstrap ++ concat progs

isVM :: String -> Bool
isVM f = take 3 (reverse f) == "mv."

main :: IO ()
main = do
  args <- getArgs
  results <- processFromPath $ head args
  con <- doesFileExist $ head args
  if con
    then writeFile (head args -<.> "asm") results
    else writeFile (head args </> takeBaseName (takeDirectory $ head args) <.> "asm") results