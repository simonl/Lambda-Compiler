module Infix 
	(fromInfix, 
	Assoc(L, R), 
	Fixity(Fixity), 
	BTree(Leaf, Node)) where
	
import Data.List




-- Infix operators to RPN		
		 


type FixityDict a = [(a, (Assoc, Int))]

data Fixity a	= Fixity a (Assoc, Int)	deriving (Show, Eq, Read)
data Assoc = L | R deriving (Show, Eq, Read)

data BTree lbl a = Leaf a 
		 | Node lbl (BTree lbl a) (BTree lbl a) 
		 deriving (Show, Eq, Read)
		 
		
		
		
fromInfix :: (Eq a) => [Fixity a] -> [Either a b] -> BTree a b
fromInfix = unfix . fmap unwrap
	where	unwrap (Fixity name stat) = (name, stat)


cmp :: (Ord a) => Assoc -> a -> a -> Bool
cmp L = (<=)
cmp R = (<)





unfix :: (Eq a) => FixityDict a -> [Either a b] -> BTree a b
unfix stats = emptyOps . foldl (uncurry shunt) ([], [])
	where	shunt out ops (Right val) = (Leaf val : out, ops)	
		shunt out ops (Left  op)  = (out2, (op, prec):ops2)
			where	(pred, prec) = getStats op stats
				(out2, ops2) = removeWhile pred out ops



removeWhile pred = helper
	where	helper out [] = (out, [])
		helper	out b@((o, p):ops) | pred p = helper (move out o) ops
					   | True   = (out, b)
					   
emptyOps (out, ops) = head $ foldl helper out ops
	where	helper out = move out . fst
	
move (r:l:out) op = (Node op l r:out)

getStats :: (Eq a) => a -> FixityDict a -> (Int -> Bool, Int)
getStats op stats  = (pred, prec)
	where	(assoc, prec) = maybe (R, 5) id $ lookup op stats
		pred p = cmp assoc p prec




dict = [Fixity "+" (L, 10), Fixity "*" (L, 5), Fixity "^" (R, 3)]
expr  = [Right 1, Left "*", Right 2, Left "+", Right 3, Left "^", Right 4, Left "*", Right 5, Left "+", Right 6]

-- 1 * 2 + 3 ^ 4 * 5 + 6
-- ((1 * 2) + ((3 ^ 4) * 5)) + 6
-- + + * 1 2 * ^ 3 4 5 6
-- 1 2 * 3 4 ^ 5 * + 6 +

