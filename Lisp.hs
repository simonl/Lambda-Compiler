import Parser
import Control.Applicative
import Control.Monad
import Data.Map as Map


data SExpLex a
	= TLex
	| FLex
	| StrLex String
	| AtomLex a
	| OpenLex
	| CloseLex
	deriving (Show, Eq)

tokens = lexical token whiteSpace
	where	token = (AtomLex <$> word) <|> true <|> false <|> string <|> open <|> close
		
		true = single '#' >> single 't' >> return TLex
		false = single '#' >> single 'f' >> return FLex
		
		string = do
			single '"'
			cs <- many (sat (/= '"')) 
			single '"'
			return (StrLex cs)
			
		open = single '(' >> return OpenLex
		close = single ')' >> return CloseLex

parse s = evalParser tokens s >>= evalParser expr
	where	expr = atom <|> true <|> false <|> string <|> list
		
		atom = do
			tok <- item
			case tok of
				AtomLex s -> return (Atom (Var s))
				_ -> mzero
		
		true = single TLex >> return (Atom T)
		false = single FLex >> return (Atom F)
		string = do
			tok <- item
			case tok of
				StrLex s -> return (Atom (Str s))
				_ -> mzero
		list = do
			single OpenLex
			es <- many expr
			single CloseLex
			return (foldr Cons Nil es)


		


data SExp a
	= Nil
	| Atom a
	| Cons (SExp a) (SExp a)
	deriving (Eq, Show)

data Value a
	= T
	| F
	| Str String
	| Var a
	| Proc (Map a (SExp (Value a))) a (SExp (Value a))
	deriving (Show, Eq)

builtins = Map.fromList [
	("lambda", lambda),
	("quote", quote),
	("read", lispRead),
	("eval", lispEval),
	("show", listPrint),
	("if", lispIf),
	("equal", lispEq),
	("cons", cons)]

lambda (Cons (Atom (Var x)) (Cons e Nil)) env = return (Atom (Proc env x e))
lambda _ _ = Nothing

quote (Cons s Nil) env = return s

lispRead (Cons x Nil) env = do
	Atom (Str s) <- eval x env
	parse s
	
listPrint (Cons x Nil) env = do
	s <- eval x env
	return (Atom (Str (show s)))
	
lispIf (Cons test (Cons t (Cons e Nil))) env = do
	Atom r <- eval test env
	case r of
	  T -> eval t env
	  F -> eval e env
	  _ -> Nothing
lispIf _ _ = Nothing

lispEq (Cons x (Cons y Nil)) env = do
	l <- eval x env
	r <- eval y env
	return (if (l == r) then (Atom T) else (Atom F))
	
cons (Cons x (Cons y Nil)) env = do
	l <- eval x env
	r <- eval y env
	return (Cons l r)

lispEval (Cons e Nil) env = do
	s <- eval e env
	evaluate s


evaluate e = eval e Map.empty

eval :: SExp (Value String) -> Map String (SExp (Value String)) -> Maybe (SExp (Value String))
eval Nil env = return Nil
eval (Atom (Var x)) env = return (env ! x)
eval (Atom v) env = return (Atom v)
eval (Cons (Atom (Var var)) x) env | Map.member var builtins = (builtins ! var) x env
eval (Cons f (Cons a Nil)) env = do
	v <- eval a env
	Atom (Proc env' x e) <- eval f env
	eval e (Map.insert x v env')
eval (Cons f _) env = Nothing


test s = parse s >>= evaluate