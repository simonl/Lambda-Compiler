module Lexer(
	Lexeme(..), lex,
	lexvar) where
import Parser
import Prelude hiding(lex)
import Control.Applicative

	-- Lexical Analysis
	 
data Lexeme	= LexVar String
		| LexLambda
		| LexOParen
		| LexCParen
		| LexDot
		deriving (Eq)
		
instance Show Lexeme where
	show (LexVar s) = s
	show LexLambda = "\\"
	show LexOParen = "("
	show LexCParen = ")"
	show LexDot = "."

lexical :: Parser a -> Parser b -> Parser [a]
lexical token white = white *> interleave token white <* white <* end


lex :: Parser [Lexeme]
lex = lexical lexeme whiteSpace
	where	lexeme	 =  (LexVar <$> word)
			<|> onChr '\\' LexLambda
			<|> onChr '.' LexDot
			<|> onChr '(' LexOParen
			<|> onChr ')' LexCParen
					


isLexVar (LexVar _) = True
isLexVar _	    = False

lexvar = sat isLexVar >>= \(LexVar s) -> return s

