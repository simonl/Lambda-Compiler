import Lexer
import Parser
import Control.Applicative
import Data.Map as Map
import Control.Monad

data SExpToken
	= SOpenParen
	| SCloseParen
	| SInt Int
	| SString String
	| SAtom String
	| STag String
	deriving (Eq, Show)

tokens = lexical token whiteSpace
  where	token	 =  onChr '(' SOpenParen
  		<|> onChr ')' SCloseParen
  		<|> (SString <$> string)
  		<|> (SInt <$> number)
  		<|> (STag <$> tag)
  		<|> (SAtom <$> atom)

	tag = (:) <$> upper <*> many (upper <|> digit)
	atom = (:) <$> lower <*> many (letter <|> digit)

tokTag = do
	x <- item
	case x of
	  STag s -> return s
	  _ -> mzero

tokAtom = do
	x <- item
	case x of
	  SAtom s -> return s
	  _ -> mzero

tokInt = do
	x <- item
	case x of
	  SInt s -> return s
	  _ -> mzero

tokStr = do
	x <- item
	case x of
	  SString s -> return s
	  _ -> mzero




type Tag = String
type Atom = String

data Value
	= VInt Int
	| VString String
	| VAtom String

data Node
	= Node Tag (Map Atom Value) [Either String Node]
	deriving (Show)

node = do
	single SOpenParen
	tag <- tokTag
	as <- Map.fromList <$> many attribute
	ns <- many child
	single SCloseParen
	return (Node tag as ns)

attribute = do
	single SOpenParen
	x <- tokAtom
	v <- value
	single SCloseParen
	return (x, v)

child = tokStr <||> node

value	 =  (VInt <$> tokInt)
	<|> (VString <$> tokStr)
	<|> (VAtom <$> tokAtom)
	
	
	

instance Show Value where
	show (VInt i) = show (show i)
	show (VString s) = show s
	show (VAtom a) = show (show a)

showHtml (Node tag as ns) = "<" ++ tag ++ showAttr as ++ ">" ++ showCh ns ++ "</" ++ tag ++ ">" 

showAttr as = Map.toList as >>= (' ':) . toStr
  where	toStr (x, v) = x ++ "=" ++ show v

showCh ns = ns >>= toStr
  where	toStr (Left s) = s
  	toStr (Right n) = showHtml n


pretty (Node tag as ns) = do
	indent <- ask
	let open = "<" ++ tag ++ showAttr as ++ ">"
	




convert :: String -> Maybe String
convert s = evalParser tokens s >>= evalParser node >>= return . showHtml

main = program "index"

program name = do
	txt <- readFile (name ++ ".shtml")
	case (convert txt) of
	  Nothing -> putStrLn "Invalid input"
	  Just html -> writeFile (name ++ ".html") html
