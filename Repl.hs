

data Exp = Index Int | Lambda Exp | Apply Exp Exp	deriving (Read)
data Closure = Closed Exp [Closure]

instance Show Closure where
	show = show . open
	
instance Show Exp where
	show (Index i) = show i
	show (Lambda e) = "(lambda " ++ show e ++ ")"
	show (Apply f x) = "(" ++ show f ++ " " ++ show x ++ ")"



	
evaluate e = eval e []
	where	eval (Index i) env = env !! i
		eval (Lambda e) env = Closed e env
		eval (Apply f x) env = apply (eval f env) (eval x env)

		apply (Closed e env) x = eval e (x : env)


open (Closed e env) = fold (Lambda e) (fmap (Just . open) env)
	where	fold (Index i) env = maybe (Index i) id (env !! i)
		fold (Lambda e) env = Lambda (fold e (Nothing : env))
		fold (Apply f x) env = Apply (fold f env) (fold x env)





main = input "> " >>= print . evaluate >>= const main

prompt p = putStr p >> getLine

input p = fmap read (prompt p)


ycomb = Lambda (Apply (Lambda (Apply (Index 0) (Index 0))) (Lambda (Apply (Index 1) (Apply (Index 0) (Index 0)))))
apply = Lambda (Lambda (Apply (Index 0) (Index 1)))