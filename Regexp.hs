import Control.Monad.State
import Control.Applicative
import Data.Map as Map

fresh = do
	x <- get
	put (succ x)
	return x
	
newtype Var = Var Int

instance Show Var where
	show (Var i) = "var" ++ show i
	
instance Enum Var where
	succ (Var n) = Var (succ n)
	pred (Var n) = Var (pred n)
	toEnum = Var
	fromEnum (Var n) = n

generate st = fst $ runState st (Var 0)

data Lambda v f
	= Lambda v (f v)
	
instance (Show v, Show (f v)) => Show (Lambda v f) where
	show (Lambda x e) = "(\\" ++ show x ++ " -> " ++ show e ++ ")"
	
close f = do
	x <- fresh
	e <- f x
	return (Lambda x e)





canMatchEmpty = rec
	where	rec Epsilon = True
		rec Fail = False
		rec (Single c) = False
		rec (Seq a b) = rec a && rec b
		rec (Alt a b) = rec a || rec b
		rec (Star r) = True










	

data RegExp
	= Epsilon
	| Fail
	| Single Char
	| Seq RegExp RegExp
	| Alt RegExp RegExp
	| Star RegExp

matchDirect re input = verify (fold re (0, input))
	where	fold Epsilon (n, xs) = Just (n, xs)
		fold Fail (n, xs) = Nothing
		fold (Single c) (n, []) = Nothing
		fold (Single c) (n, x:xs) | c == x = Just (n+1, xs)
					  | otherwise = Nothing
		fold (Seq a b) (n, xs) = case (fold a (n, xs)) of
						Nothing -> Nothing
						Just (m, ys) -> fold b (m, ys)
		fold (Alt a b) (n, xs) = case (fold a (n, xs)) of
						Nothing -> fold b (n, xs)
						Just (m, ys) -> Just (m, ys)
		fold (Star r) (n, xs) = case (fold r (n, xs)) of
						Nothing -> Just (n, xs)
						Just (m, ys) | n == m -> Just (n, xs)
							     | otherwise -> fold (Star r) (m, ys)

		verify Nothing = False
		verify (Just (n, [])) = True
		verify (Just (n, x:xs)) = False











{--

matcherDirect re xs = verify (fold re <(0, ~xs)>)
	where	fold Epsilon xs = <Just ~xs>
		fold Fail xs = <Nothing>
		fold (Single c) xs = <case ~xs of
					(n, []) -> Nothing
					(n, x:xs) | c == x -> Just (n+1, xs)
						  | otherwise -> Nothing>
		fold (Seq a b) xs = <case ~(fold a xs) of
					Nothing -> Nothing
					Just ys -> ~(fold b <ys>)>
		fold (Alt a b) xs = <case ~(fold a xs) of
					Nothing -> ~(fold b xs)
					Just ys -> Just ys>
		fold (Star r) xs =
			<let loop (n, xs) = case ~(fold r <(n, xs)>) of
						Nothing -> Just (n, xs)
						Just (m, ys) | n == m -> Just (n, xs)
							     | otherwise -> loop (m, ys)
			 in loop ~xs>

		verify out = <case ~out of
				Nothign -> False
				(n, []) -> True
				(n, x:xs) -> False>

--}

data Input v
	= Name v
	| Init v
	| Tuple v v

instance (Show v) => Show (Input v) where
	show (Name xs) = show xs
	show (Init xs) = "(0, " ++ show xs ++ ")"
	show (Tuple n xs) = "(" ++ show n ++ ", " ++ show xs ++ ")"
	
data Expr v
	= EJust (Input v)
	| ENothing
	| ESingle (Input v) Char v v
	| ESeq (Expr v) v (Expr v)
	| EAlt (Expr v) (Expr v)
	| EStar (Input v) v v v (Expr v) v v
	
instance (Show v) => Show (Expr v) where
	show (EJust xs) = "(Just " ++ show xs ++ ")"
	show ENothing = "Nothing"
	show (ESingle xs c n rest) = 
		"(case " ++ show xs ++ " of { (" ++ 
		show n ++ ", " ++ show c ++ ":" ++ show rest ++ 
		") -> Just (1+" ++ show n ++ ", " ++ show rest ++ "); _ -> Nothing })"
	show (ESeq a ys b) = 
		"(case " ++ show a ++ " of { Nothing -> Nothing; " ++ 
		"Just " ++ show ys ++  " -> " ++ show b ++ " })"
	show (EAlt a b) = "(case " ++ show a ++ " of { Nothing -> " ++ show b ++ "; r -> r })"
	show (EStar vec loop n xs r m ys) =
		"(let { " ++ show loop ++ " (" ++ show n ++ ", " ++ show xs ++ ") = " ++
		"(case " ++ show r ++ " of { Just (" ++ show m ++ ", " ++ show ys ++ ") | " ++
		show n ++ " /= " ++ show m ++ " -> " ++ show loop ++ " (" ++ show m ++ ", " ++ show ys ++ ");" ++
		" _ -> Just (" ++ show n ++ ", " ++ show xs ++ ") }) " ++
		"} in " ++ show loop ++ " " ++ show vec ++ ")"

data Output v
	= Verify (Expr v)

instance (Show v) => Show (Output v) where
	show (Verify out) = "(case " ++ show out ++ " of { Just (_, []) -> True; _ -> False })"

matcherDirect re input = Verify <$> fold re (Init input)
	where	fold Epsilon xs = return (EJust xs)
		fold Fail xs = return ENothing
		fold (Single c) xs = do
			n <- fresh
			rest <- fresh
			return (ESingle xs c n rest)
		fold (Seq a b) xs = do
			ea <- fold a xs
			ys <- fresh
			eb <- fold b (Name ys)
			return (ESeq ea ys eb)
		fold (Alt a b) xs = do
			ea <- fold a xs
			eb <- fold b xs
			return (EAlt ea eb)
		fold (Star r) vec = do
			loop <- fresh
			n <- fresh
			xs <- fresh
			m <- fresh
			ys <- fresh
			er <- fold r (Tuple n xs)
			return (EStar vec loop n xs er m ys)


makeMatcherDirect re = generate $ close (matcherDirect re)

















matchCPS re input = rec re (0, input) verify
	where	verify (Just (n, [])) = True
		verify _ = False
		
		rec Epsilon xs k = k (Just xs)
		rec Fail xs k = k Nothing
		rec (Single c) (n, []) k = k Nothing
		rec (Single c) (n, x:xs) k | c == x = k (Just (1+n, xs))
					   | otherwise = k Nothing
		rec (Seq a b) xs k = rec a xs (\ra -> case ra of
						Nothing -> k Nothing
						Just ys -> rec b ys k)
		rec (Alt a b) xs k = rec a xs (\ra -> case ra of
						Nothing -> rec b xs k
						Just ys -> k (Just ys))
		rec (Star a) (n, xs) k = rec a (n, xs) (\ra -> case ra of
						Just (m, ys) | n /= m -> rec (Star a) (m, ys) k
						_ -> k (Just (n, xs)))





data Cont
	= Done
	| SeqFst RegExp Cont
	| AltFst RegExp (Int, [Char]) Cont
	| ContStar RegExp (Int, [Char]) Cont
	
matchDefCPS re input = rec re (0, input) Done
	where	rec Epsilon xs k = return k xs
		rec Fail xs k = fail k
		rec (Single c) (n, []) k = fail k
		rec (Single c) (n, x:xs) k | c == x = return k (1+n, xs)
					   | otherwise = fail k
		rec (Seq a b) xs k = rec a xs (SeqFst b k)
		rec (Alt a b) xs k = rec a xs (AltFst b xs k)
		rec (Star a) xs k = rec a xs (ContStar a xs k)

		fail Done = False
		fail (SeqFst b k) = fail k
		fail (AltFst b xs k) = rec b xs k
		fail (ContStar a xs k) = return k xs
		
		return Done (n, []) = True
		return Done (n, x:xs) = False
		return (SeqFst b k) ys = rec b ys k
		return (AltFst b xs k) ys = return k ys
		return (ContStar a (n, xs) k) (m, ys)	| n == m = return k (n, xs)
							| otherwise = rec (Star a) (m, ys) k
		
		
		
		


{--

matcher re input = rec re <(0, ~input)> Done
	where	rec Epsilon xs k = return k xs
		rec Fail xs k = fail k
		rec (Single c) xs k = <case ~xs of
					(n, x:xs) | c == x -> ~(return k <(1+n, xs)>)
					_ -> ~(fail k)>
		rec (Seq a b) xs k = rec a xs (SeqFst b k)
		rec (Alt a b) xs k = rec a xs (AltFst b xs k)
		rec (Star a) vec k =
			<let loop xs = ~(rec a <xs> (ContStar <loop> <xs> k))
			 in loop ~vec>
		
		fail Done = <False>
		fail (SeqFst b k) = fail k
		fail (AltFst b xs k) = rec b xs k
		fail (ContStar a xs k) = return k xs
		
		return Done xs = <case ~xs of
					(n, []) -> True
					_ -> False>
		return (SeqFst b k) ys = rec b ys k
		return (AltFst b xs k) ys = return k ys
		return (ContStar loop xs k) ys = <let (n, xs) = ~xs
						   (m, ys) = ~ys
						in case (n == m) of
							True -> ~(return k xs)
							False -> ~loop (m, ys)>

--}
	
instance (Show v) => Show (ExprK v) where
	show EKFalse = "False"
	show (EKVerif xs) = "(case " ++ show xs ++ " of { (_, []) -> True; _ -> False })"
	show (EKSingle xs c n rest m win fail) =
		"(case " ++ show xs ++ " of { (" ++ show n ++ ", " ++ show c ++ ":" ++ show rest ++ ") -> " ++
		"(let { " ++ show m ++ " = 1 + " ++ show n ++ " } in " ++ show win ++ "); _ -> " ++ show fail ++ "})"
	show (EKLoop vec loop xs body) =
		"(let { " ++ show loop ++ " " ++ show xs ++ " = " ++ show body ++ " } in " ++ 
		show loop ++ " " ++ show vec ++ ")"
	show (EKCheck old new loop n xs m ys stop) =
		"(let { " ++ show (Tuple n xs) ++ " = " ++ show old ++ "; " ++ 
		show (Tuple m ys) ++ " = " ++ show new ++ " } in " ++
		"(case " ++ show n ++ " == " ++ show m ++ " of { True -> " ++ show stop ++ "; False -> " ++
		show loop ++ " " ++ show (Tuple m ys) ++ "} ) )"

data ExprK v
	= EKFalse
	| EKVerif (Input v)
	| EKSingle (Input v) Char v v v (ExprK v) (ExprK v)
	| EKLoop (Input v) v v (ExprK v)
	| EKCheck (Input v) (Input v) v v v v v (ExprK v)

data GCont v
	= GDone
	| GSeqFst RegExp (GCont v)
	| GAltFst RegExp (Input v) (GCont v)
	| GContStar v (Input v) (GCont v)

matcherDefCPS re input = rec re (Init input) GDone
	where	rec Epsilon xs k = returnK k xs
		rec Fail xs k = failK k
		rec (Single c) xs k = do
			n <- fresh
			rest <- fresh
			m <- fresh
			ret <- returnK k (Tuple m rest)
			fl <- failK k
			return (EKSingle xs c n rest m ret fl)
		rec (Seq a b) xs k = rec a xs (GSeqFst b k)
		rec (Alt a b) xs k = rec a xs (GAltFst b xs k)
		rec (Star a) vec k = do
			loop <- fresh
			xs <- fresh
			ra <- rec a (Name xs) (GContStar loop (Name xs) k)
			return (EKLoop vec loop xs ra)

		failK GDone = return EKFalse
		failK (GSeqFst b k) = failK k
		failK (GAltFst b xs k) = rec b xs k
		failK (GContStar loop xs k) = returnK k xs

		returnK GDone ys = return (EKVerif ys)
		returnK (GSeqFst b k) ys = rec b ys k
		returnK (GAltFst b xs k) ys = returnK k ys
		returnK (GContStar loop old k) new = do
			n <- fresh
			xs <- fresh
			m <- fresh
			ys <- fresh
			ra <- returnK k (Tuple n xs)
			return (EKCheck old new loop n xs m ys ra)



makeMatcherCPS re = generate $ close (matcherDefCPS re)




		
		
		

