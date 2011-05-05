module Parser where

import Control.Applicative
import Data.Monoid hiding (Last)
import Control.Monad.State
import Data.Char


-- Parser 

type ParserT b = StateT [b] Maybe
type Parser = ParserT Char

parser = StateT
runParser = runStateT
evalParser = evalStateT
 

item :: ParserT a a
item = parser $ \s -> case s of
	[]	-> mzero
	c:cs	-> return (c, cs)

end :: ParserT a ()
end = parser $ \s -> case s of
	[]	-> return ((), s)
	c:cs	-> mzero


sat :: (a -> Bool) -> ParserT a a
sat = flip filter' item

single :: (Eq a) => a -> ParserT a a
single c = sat (== c)

allOf :: (Eq a) => [a] -> ParserT a [a]
allOf = sequence . fmap single

oneOf :: (Eq a) => [a] -> ParserT a a
oneOf = msum . fmap single

upper  = sat isUpper
lower  = sat isLower
letter = sat isLetter

word   = (:) <$> lower <*> many letter
capitalised = (:) <$> upper <*> many letter

sym = oneOf "!+:*/%=$^&|-<>~,.?"
valueSymbol = allOf "[]" <|> allOf "{}" <|> allOf "()"
symbol = some sym

digit = sat isDigit

number :: Parser Int
number = read <$> some digit


space = sat isSpace
whiteSpace = many space

interleave :: ParserT a b -> ParserT a c -> ParserT a [b]
interleave main sep = (:) <$> main <*> many (sep *> main)

on :: ParserT a b -> c -> ParserT a c
on p v = const v <$> p

onChr = on . single
onStr = on . allOf 
onOne = on . oneOf

alternate :: ParserT s a -> ParserT s b -> ParserT s [Either b a]
alternate main sep = helper
	where	helper  = cons main2 (helper' <|> return [])
		helper' = cons sep2 helper
		main2 = Right <$> main
		sep2  = Left  <$> sep
		
		cons mx mxs = (:) <$> mx <*> mxs

sepBy sep main = interleave main (single sep)

(<||>) :: (Alternative f) => f a -> f b -> f (Either a b)
p <||> q = Left <$> p <|> Right <$> q


-- Utilities

filter' :: (MonadPlus m) => (a -> Bool) -> m a -> m a
filter' p ma = do
	a <- ma
	guard (p a)
	return a

instance (Monad m) => Applicative (StateT s m) where
	pure = return
	(<*>) = ap

instance (MonadPlus m) => Alternative (StateT s m) where
	empty = mzero
	(<|>) = mplus
	