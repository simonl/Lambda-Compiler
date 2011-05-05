import Control.Applicative
import Prelude hiding(lex)
import System.IO
import Data.Map
import Data.List
import Data.Monoid
import Control.Monad.Reader
import Infix  
import Lexer
import Parser
import Control.Monad.State
import Data.Set as Set
import Control.Monad.Writer


-- Stuff

skip x y = y

fresh = Main.update succ
update f = do
	x <- get
	modify f
	return x
reset = put minBound

evalWriter = fst . runWriter

instance Applicative (Reader e) where
	pure = return
	(<*>) = ap

newtype MapM k v = MapM { runMap :: Map k v }	deriving (Show, Eq)

instance (Ord k, Monoid v) => Monoid (MapM k v) where
	mempty = MapM mempty
	MapM m1 `mappend` MapM m2 = MapM $ Data.Map.unionWith mappend m1 m2
	


showSet set = "{" ++ intersperse ',' str ++ "}"
	where	str = Set.fold (++) [] (Set.map show set)

instance (Monoid w) => Applicative (Writer w) where
	pure = return
	(<*>) = ap
	
instance (Monad m) => Applicative (ReaderT e m) where
	pure = return
	(<*>) = ap

instance (Monoid w, Monad m) => Applicative (WriterT w m) where
	pure = return
	(<*>) = ap
	
partitionEithers = foldr part ([], [])
	where	part (Left l) (ls, rs) = (l:ls, rs)
		part (Right r) (ls, rs) = (ls, r:rs)
	
fromJust (Just x) = x
fromJust Nothing  = error "Maybe value was not Just after all!"

uncurry3 f (a, b, c) = f a b c

if' b t e = if b then t else e

(|>) :: a -> (a -> b) -> b
x |> f = f x

m <> n = m `mappend` n

head' [] = Nothing
head' (x:_) = Just x

tail' [] = []
tail' (_:xs) = xs


loeb fs = let res = fmap (\f -> f res) fs in res 




	-- Syntactic Analysis

parse :: ParserT Lexeme MultiExp
parse = expression <* end
	where	expression = application
		application = MApply <$> value <*> many value
		
		value	 =  variable 
			<|> lambda
			<|> inparen
			
		variable = MVar <$> lexvar
		lambda = single LexLambda *> (MLambda <$> some lexvar <*> (single LexDot *> expression))			
		inparen = single LexOParen *> expression <* single LexCParen


type Nat = Int
newtype Ident = Ident { unIdent :: Nat }	deriving (Eq, Bounded, Ord)
newtype Regis = Regis Nat			deriving (Eq)

instance Enum Ident where
	succ = Ident . succ . unIdent
	pred = Ident . pred . unIdent
	toEnum = Ident . toEnum
	fromEnum = fromEnum . unIdent
	enumFrom = fmap Ident . enumFrom . unIdent

instance Show Ident where
	show (Ident i) = 'L' : show i
	
list sep xs = concat (intersperse sep xs)
plist = list ", " . fmap show

instance Show MultiExp where
	show (MVar x) = x
	show (MLambda xs e) = "(lambda (" ++ list " " xs ++ ") " ++ show e ++ ")"
	show (MApply f xs) = "(" ++ show f ++ " " ++ list " " (fmap show xs) ++ ")"
	
instance Show SimpleExp where
	show (SVar x) = x
	show (SLambda x e) = "(lambda " ++ x ++ " " ++ show e ++ ")"
	show (SApply f x) = "(" ++ show f ++ " " ++ show x ++ ")"

instance Show UniqExp where
	show (UIdent id) = show id
	show (ULambda id body) = "(lambda " ++ show id ++ " " ++ show body ++ ")"
	show (UApply f x) = "(" ++ show f ++ " " ++ show x ++ ")"
	
instance Show ThunkExp where
	show (HIdent x) = show x
	show (HLambda xs body) = "(lamdba (" ++ plist xs ++ ") " ++ show body ++ ")"
	show (HApply f xs) = "(" ++ show f ++ (xs >>= \x -> ' ' : show x) ++ ")"

instance Show KVal where
	show v = runReader (foldCont lambda current cont apply klet ret v) ""
		where	lambda xs fe = do
				e <- local ('\t':) fe
				indent <- ask
				return ("(" ++ plist xs ++ "){\n" ++ e ++ "\n" ++ indent ++ "}")
			
			apply f xs fk = fk (show f ++ "(" ++ plist xs ++ ")")
			ret fk xs = fk (plist xs)
			klet fk fv = fv >>= fk
			
			cont xs fe k = do
				e <- fe
				indent <- ask
				return (indent ++ plist xs ++ " = " ++ k ++ "\n" ++ e)
			
			current k = ask >>= \indent -> return (indent ++ "return: " ++ k)

instance (Show a) => Show (NVal a) where
	show v = foldAnn lambda current cont apply nlet ret v ""
		where	lambda info xs fe indent = show info ++ " (" ++ plist xs ++ "){\n" ++ fe ('\t':indent) ++ "\n" ++ indent ++ "}"
			current s indent = indent ++ "return: " ++ s
			cont xs fe s indent = indent ++ plist xs ++ " = " ++ s ++ "\n" ++ fe indent
			apply f xs fk indent = fk (show f ++ "(" ++ plist xs ++ ")") indent
			nlet fk fv indent = fk (fv indent) indent
			ret fk xs indent = fk (plist xs) indent

instance Show RVal where
	show v = runReader (foldClos lambda tuple apply proj cons dest ret current cont v) ""
		where	cons fk fv = fv >>= fk
			dest fk fe = fe >>= fk
			ret fk xs = fk (plist xs)

			tuple xs = return ("[" ++ plist xs ++ "]")
			lambda xs fbody = do
				body <- local ('\t':) fbody
				indent <- ask
				return ("(" ++ plist xs ++ "){\n" ++ body ++ "\n" ++ indent ++ "}")

			current e = ask >>= \indent -> return (indent ++ "return: " ++ e)
			cont xs fbody e = do
				body <- fbody
				indent <- ask 
				return (indent ++ plist xs ++ " = " ++ e ++ "\n" ++ body)

			proj i x = return (show x ++ "[" ++ show i ++ "]")
			apply f xs = return (show f ++ "(" ++ plist xs ++ ")")


instance Show LGlobal where
	show g = showG g
		where	showG (LLambda xs e) = "(" ++ plist xs ++ "){\n" ++ showB e ++ "\n}"
			showG (LTuple xs) = "[" ++ plist xs ++ "]"
			
			showLV (LValue x i) = show x ++ "[" ++ show i ++ "]"
			
			showC LCurrent s = "\treturn: " ++ s
			showC (LCont xs e) s = "\t" ++ plist xs ++ " = " ++ s ++ "\n" ++ showB e
			
			showE (RApply f xs) = show f ++ "(" ++ plist xs ++ ")"
			showE (RProj i x) = show x ++ "[" ++ show i ++ "]"
			
			showB (LAlloc k n) = showC k (show n ++ "[]")
			showB (LDest k e) = showC k (showE e)
			showB (LAssign lval x e) = "\t" ++ showLV lval ++ " := " ++ show x ++ "\n" ++ showB e
			showB (LReturn k xs) = showC k (plist xs)
	

instance Show BGlobal where
	show = foldBruijn lambda tuple current cont alloc dest apply proj assign ret
		where	lambda n se = "(" ++ show n ++ "){\n" ++ se ++ "\n}"
			tuple xs = "[" ++ plist xs ++ "]"
		
			alloc sk n = sk ("new " ++ show n ++ "[]")
			dest sk se = sk se
			assign (BRef x i) y fe = "\t" ++ show x ++ "[" ++ show i ++ "] = " ++ show y ++ "\n" ++ fe
			ret fk xs = fk (plist xs)
		
			current t se = "\treturn: " ++ se
			cont n sb se = "\t^ " ++ se ++ "\n" ++ sb
		
			apply f xs = show f ++ "(" ++ plist xs ++ ")"
			proj n x = show x ++ "[" ++ show n ++ "]"

instance Show BValue where
	show (BGlobal id) = show id
	show (BLocal i) = '#' : show i




-- AST
data MultiExp	= MVar String
		| MLambda [String] MultiExp
		| MApply MultiExp [MultiExp]

-- Curried
data SimpleExp	= SVar String
		| SLambda String SimpleExp
		| SApply SimpleExp SimpleExp

-- Uniques
data UniqExp	= UIdent Ident
		| ULambda Ident UniqExp
		| UApply UniqExp UniqExp

-- By Name	0/1 argument functions, used [] instead of Maybe
data ThunkExp	= HIdent Ident
		| HLambda [Ident] ThunkExp
		| HApply ThunkExp [ThunkExp]

-- Continuations
data CVal	= CIdent Ident
		| CLambda [Ident] CBlock
		deriving (Show)
data CCont	= CCurrent
		| CCont [Ident] CBlock
		deriving (Show)
data CBlock	= CApply CVal [CVal] CCont
		| CReturn CCont [CVal]
		deriving (Show)

-- Normalized Continuations
data KVal	= KLambda [Ident] KBlock
data KCont	= KCurrent
		| KCont [Ident] KBlock
data KBlock	= KApply Ident [Ident] KCont
		| KLet KCont KVal
		| KReturn KCont [Ident]

-- Free variable annotations
data NVal a	= NLambda a [Ident] (NBlock a)
data NCont a	= NCurrent
		| NCont [Ident] (NBlock a)
data NBlock a	= NApply Ident [Ident] (NCont a)
		| NReturn (NCont a) [Ident]
		| NLet (NCont a) (NVal a)

-- Explicit Closures
data RVal	= RLambda [Ident] RBlock
		| RTuple [Ident]
data RExp	= RApply Ident [Ident]
		| RProj Nat Ident
data RCont	= RCurrent
		| RCont [Ident] RBlock
data RBlock	= RCons RCont RVal
		| RDest RCont RExp
		| RReturn RCont [Ident]

-- constants and functions Lifted to top level (TO DO EARLIER)
data LGlobal	= LLambda [Ident] LBlock
		| LTuple [Ident]

data LValue	= LValue Ident Nat
		
data LCont	= LCurrent
		| LCont [Ident] LBlock
		
data LBlock	= LAlloc LCont Nat
		| LDest LCont RExp
		| LAssign LValue Ident LBlock
		| LReturn LCont [Ident]



-- Debruijn
data BGlobal	= BLambda Nat BBlock
		| BTuple [Ident]

data BValue	= BGlobal Ident
		| BLocal Nat

data BRef	= BRef BValue Nat

data BExp	= BApply BValue [BValue]
		| BProj Nat BValue
		
data BCont	= BCurrent Nat
		| BCont Nat BBlock

data BBlock	= BAlloc BCont Nat
		| BDest BCont BExp
		| BAssign BRef BValue BBlock
		| BReturn BCont [BValue]

		


-- Primitive Recursion
foldMulti var lambda apply = fold
	where	fold (MVar x) = var x
		fold (MLambda xs e) = lambda xs (fold e)
		fold (MApply f xs) = apply (fold f) (fmap fold xs)
		
foldSimple var lambda apply = fold
	where	fold (SVar x) = var x
		fold (SLambda x e) = lambda x (fold e)
		fold (SApply f x) = apply (fold f) (fold x)

foldUniq ident lambda apply = fold
	where	fold (UIdent x) = ident x
		fold (ULambda x e) = lambda x (fold e)
		fold (UApply f x) = apply (fold f) (fold x)

foldThunk ident lambda apply = fold
	where	fold (HIdent x) = ident x
		fold (HLambda xs e) = lambda xs (fold e)
		fold (HApply f xs) = apply (fold f) (fmap fold xs)

foldCCont lambda ident current cont apply ret = foldV
	where	foldV (CLambda xs e) = lambda xs (foldB e)
		foldV (CIdent x) = ident x
		
		foldC CCurrent = current
		foldC (CCont xs e) = cont xs (foldB e)
		
		foldB (CApply f xs k) = apply (foldV f) (fmap foldV xs) (foldC k)
		foldB (CReturn k xs) = ret (foldC k) (fmap foldV xs)

		
		
foldCont lambda current cont apply klet ret = foldV
	where	foldV (KLambda xs e) = lambda xs (foldB e)
		
		foldC KCurrent = current
		foldC (KCont xs e) = cont xs (foldB e)
		
		foldB (KApply f xs k) = apply f xs (foldC k)
		foldB (KReturn k xs) = ret (foldC k) xs
		foldB (KLet k v) = klet (foldC k) (foldV v)

foldAnn lambda current cont apply nlet ret = foldV
	where	foldV (NLambda info xs e) = lambda info xs (foldB e)
		
		foldC NCurrent = current
		foldC (NCont xs e) = cont xs (foldB e)
		
		foldB (NApply f xs k) = apply f xs (foldC k)
		foldB (NReturn k xs) = ret (foldC k) xs
		foldB (NLet k v) = nlet (foldC k) (foldV v)
		
foldClos lambda tuple apply proj cons dest ret current cont = foldVal
	where	foldVal (RLambda xs e) = lambda xs (foldBlock e)
		foldVal (RTuple xs) = tuple xs
		
		foldExpr (RApply f xs) = apply f xs
		foldExpr (RProj i x) = proj i x
		
		foldBlock (RCons k v) = cons (foldCont k) (foldVal v)
		foldBlock (RDest k e) = dest (foldCont k) (foldExpr e)
		foldBlock (RReturn k xs) = ret (foldCont k) xs
		
		foldCont RCurrent = current
		foldCont (RCont xs e) = cont xs (foldBlock e)

foldGlobal lambda tuple current cont alloc dest apply proj assign ret = foldG
	where	foldG (LLambda xs e) = lambda xs (foldB e)
		foldG (LTuple xs) = tuple xs
		
		foldB (LAlloc k n) = alloc (foldK k) n
		foldB (LDest k ex) = dest (foldK k) (foldE ex)
		foldB (LAssign lv x e) = assign lv x (foldB e)
		foldB (LReturn k xs) = ret (foldK k) xs
		
		foldK LCurrent = current
		foldK (LCont xs e) = cont xs (foldB e)
		
		foldE (RApply f xs) = apply f xs
		foldE (RProj n x) = proj n x

foldBruijn lambda tuple current cont alloc dest apply proj assign ret = foldG
	where	foldG (BLambda n e) = lambda n (foldB e)
		foldG (BTuple xs) = tuple xs
		
		foldB (BAlloc k n) = alloc (foldK k) n
		foldB (BDest k e) = dest (foldK k) (foldE e)
		foldB (BAssign lv x e) = assign lv x (foldB e)
		foldB (BReturn k xs) = ret (foldK k) xs
		
		foldK (BCurrent t) = current t
		foldK (BCont n e) = cont n (foldB e)
		
		foldE (BApply f xs) = apply f xs
		foldE (BProj n x) = proj n x

{--

Y = \f -> (\x -> x x) (\y -> f (y y))




(\a b c -> e) s t u

(((\a. \b. \c. e) s) t) u




--

evaluate e = eval e (\i -> error "Index out of Bounds")
	where	eval (Index i) env = env i
		
		eval (Lambda e) env = \x -> eval e (extend x env)
		eval (Pair a b) env = \f -> f fst snd
			where	fst = eval a env
				snd = eval b env
		eval (Inl e) env = \k c -> k v
			where	v = eval e env
		eval (Inr e) env = \k c -> c v
			where	v = eval e env
		
		eval (Apply f x) env = (eval f env) (eval x env)
		eval (Fst e) env = (eval e env) (\a b -> a)
		eval (Snd e) env = (eval e env) (\a b -> b)
		eval (Case e l r) env = (eval e env) (\x -> eval l (extend x env)) (\x -> eval r (extend x env))
		
		extend x env 0 = x
		extend x env (1+n) = env n

evaluate e k = eval e [] k
	where	eval (Index i) env k = k (env !! i)
		
		eval (Lambda e) env k = k \x k -> eval e (x:env) k
		eval (Pair a b) env k = eval a env \fst -> eval b env \snd -> k \f -> f fst snd
		eval (Inl e) env k = k \k c -> eval e env k
		eval (Inr e) env k = k \k c -> eval e env c
		
		eval (Apply f x) env k = eval f env \g -> eval x env \y -> g y k
		eval (Fst e) env k = eval e env \p -> p (\a b -> k a)
		eval (Snd e) env k = eval e env \p -> p (\a b -> k b)
		eval (Case e l r) env k = eval e env \v -> v (\x -> eval l (x:env) k) (\x -> eval r (x:env) k)

evaluate e k = eval e [] k
	where	eval (Index i) env k = throw k (env !! i)
		
		eval (Lambda e) env k = throw k (Closed e env)
		eval (Pair a b) env k = eval a env (TupFst b env k)
		eval (Inl e) env k = eval e env (InLeft k)
		eval (Inr e) env k = eval e env (InRight k)
		
		eval (Apply f x) env k = eval x env (Arg f env k)
		eval (Fst e) env k = eval e env (ProjFst k)
		eval (Snd e) env k = eval e env (ProjSnd k)
		eval (Case e l r) env k = eval e env (Scrut l r env k)
		
		throw (Arg f env k) y = eval f env (Func y k)
		throw (Func y k) (Closed e env) = eval e (y:env) k
		
		throw (TupFst b env k) fst = eval b env (TupSnd fst k)
		throw (TupSnd fst k) snd = throw k (Tuple fst snd)
		throw (ProjFst k) (Tuple fst snd) = throw k fst
		throw (ProjSnd k) (Tuple fst snd) = throw k snd
		
		throw (InLeft k) v = throw k (Left v)
		throw (InRight k) v = throw k (Right v)
		throw (Scrut l r env k) (Left v) = eval l (v:env) k
		throw (Scrut l r env k) (Right v) = eval r (v:env) k
		


uX. X -> X

uX. Lazy X -> X
	Lazy = \a. (T -> a) \/ a

uX. Lazy X => X
	Lazy = \a. (T => a) \/ a
	(=>) = \a b. Exists e. (e /\ a -> b) /\ e
	
uX. Ref (Lazy X) => X
	Lazy = \a. (T => a) \/ a
	(=>) = \a b. Exists e. (Ref e /\ a -> b) /\ Ref e
	
uX. ~(Ref (Lazy X) /\ ~X)
	Lazy = \a. ~~a \/ a
	(~)  = \a. a => _|_
	(=>) = \a b. Exists e. (Ref e /\ a -> b) /\ Ref e


\x. \y. x

fold \x. fold \y. x

fold \x. fold \y. force x

fold (pack (\e x. fold (pack (\e y. force e, x)), &()))

\k. {
  code = \e x k. {
    inner = \e y k. {
      z = force x
      return(k, z)
    }
    pair = (inner, x)
    clos = fold pair
    univ = fold clos
    return(k, clos)
  }
  unit = ()
  env = &unit
  pair = (code, env)
  clos = pack pair
  univ = fold clos
  return(k, univ)
}
			
cont (Variable x) = Lambda unit (Return Current (Variable x))
cont (Lambda x e) = Lambda unit (Return Current (Lambda x body))
	where	Lambda _ body = cont e
cont (Apply f x) = Lambda unit (Apply (cont f) unit (Cont g $
				Apply (cont x) unit (Cont y $
				Apply (Variable g) (Variable y) Current)))
								
inline = value
	where	value (Variable x) = Variable x
		value (Lambda x e) = Lambda x (block e Current)
		
		block (Apply (Lambda y e) x k) cc = block (Return (Cont y e) x) (cont k cc)
		block (Apply f x k) cc = Apply (value f) (value x) (cont k cc)
		block (Return k x) cc = Return (cont k cc) (value x)
		
		cont Current cc = cc
		cont (Cont x e) cc = Cont x (block e cc)

alias v = value v empty
	where	value (Variable x) env = Variable (lookup x env)
		value (Lambda x e) env = Lambda x (block e env)
		
		block (Apply f x k) env = Apply (value f env) (value x env) (kont k env)
		block (Return k x) env = case (value x env) of
			Variable y -> cont k (Alias y) env
			v	   -> cont k (Ret v) env
		
		cont k (Ret v) env = Return (kont k env) v
		cont Current (Alias y) env = Return Current (Variable y)
		cont (Cont x e) (Alias y) env = block e (insert x y env)
		
		kont Current env = Current
		kont (Cont x e) env = Cont x (block e env)

		data Kont v = App v v | Alias Ident | Ret v



mu = expFold $ emptyFold {
	variable = Variable,
	lambda x fe = Fold (Lambda x fe),
	apply ff fx = Apply (Unfold ff) fx
}

byname = expFold $ emptyFold {
	variable = Force . Variable,
	lambda = Lambda,
	apply ff fx = Apply ff (delay fx),
	fold = Fold,
	unfold = Unfold
}

delay (Force (Variable x)) = Variable x
delay t@(Fold (Lambda x e)) = Variant 0 t
delay t@(Apply (Unfold f) x) = Variant 1 t

data ExpFold b = ExpFold {
	variable :: Ident -> b,
	lambda :: Ident -> b -> b,
	tuple :: [b] -> b,
	variant :: Nat -> b -> b,
	fold :: b -> b,
	pack :: b -> b,
	ref :: b -> b,
	apply :: b -> b -> b,
	project :: Nat -> b -> b,
	case :: b -> [(Ident, b)] -> b,
	unfold :: b -> b,
	deref :: b -> b,
	unpack :: b -> (Ident, b) -> b
}

emptyFold = ExpFold {
	variable = undefined,
	lambda = undefined,
	tuple = undefined,
	variant = undefined,
	fold = undefined,
	pack = undefined,
	ref = undefined,
	apply = undefined,
	project = undefined,
	case = undefined,
	unfold = undefined,
	deref = undefined,
	unpack = undefined	
}

expFold efold = rec
	where	rec (Variable x) = variable efold x
		rec (Lambda x e) = lambda efold x (rec e)
		rec (Tuple xs) = tuple efold (fmap rec xs)
		rec (Variant n x) = variant efold n (rec x)
		rec (Fold x) = fold efold (rec x)
		rec (Pack x) = pack efold (rec x)
		rec (Ref x) = ref efold (rec x)
		rec (Apply f x) = apply efold (rec f) (rec x)
		rec (Project n x) = project efold n (rec x)
		rec (Case x ks) = case efold (rec x) (fmap (fmap rec) ks)
		rec (Unfold x) = unfold efold (rec x)
		rec (Deref x) = deref efold (rec x)
		rec (Unpack x) = unpack efold (rec x)
		
		
		

-- Complete

data Type	= Sum [Type]
		| Product [Type]
		| Exponent Type Type
		| Mu Ident Type
		| Reference Type
		| Exists Ident Type
		| TVar Ident

data Exp	= Variable Ident
		| Lambda Ident Exp
		| Tuple [Exp]
		| Variant Nat Exp
		| Fold Exp
		| Ref Exp
		| Pack Exp
		| Apply Exp Exp
		| Project Nat Exp
		| Case Exp [(Ident, Exp)]
		| Unfold Exp
		| Deref Exp
		| Unpack Exp (Ident, Exp)
		| Force Exp

data Cont	= Current
		| Cont Ident Block
		| Assign Ident Block
data Value	= Lambda Ident Block
		| Tuple [Ident]
		| Variant Nat Ident
		| Ref Ident
		| Pack Ident
		| Fold Ident
data Block	= Let Cont Value
		| Apply Ident Ident Cont
		| Project Nat Ident Cont
		| Case Ident [Cont]
		| Unfold Ident Cont
		| Deref Ident Cont
		| Unpack Ident Cont
		| Return Cont Ident


	
-- Simple Types
data Type	= Sum [Type]
		| Product [Type]
		| Exponent Type Type

data Exp	= Variable Ident
		| Lambda Ident Exp
		| Tuple [Exp]
		| Variant Nat Exp
		| Apply Exp Exp
		| Project Nat Exp
		| Case Exp [(Ident, Exp)]
		| Reference Exp
		| Deref Exp
		| Force Exp
		| Rec Exp

data Cont	= Current
		| Cont Ident Block
data Value	= Lambda Ident Block
		| Tuple [Ident]
		| Variant Nat Ident
data Block	= Let Cont Value
		| Apply Ident Ident Cont
		| Project Nat Ident Cont
		| Case Ident [Cont]
		| Return Cont Ident


data Hang = Hang [Char] {Char} Int
data Result = Used | Error Hang | Found Hang

play :: Hang -> Char -> Result
play (Hang word used err) c	| c `elem` used = Used
				| c `elem` word = Found (Hang word (insert c used) err)
				| otherwise	= Error (Hang word (insert c used) (err + 1))

game word = loop (Hang word empty 0)
	where	loop hang = do
			print hang
			c <- getChar
			case (play hang) of
				Used -> putLine "Already used" >> loop hang
				Error (Hang w u e) | e < 6 -> putLine "Incorrect letter" >> loop hang
						   | otherwise -> putLine "You lose" >> print hang
				Found hang -> putLine "Great job" >> loop hang

instance Show Hang where
	show (Hang word used errs) = drawMan errs ++ "\n" ++ hidden ++ " -- " ++ show used
		where	hidden = for word $ \l -> if (l `elem` used) then l else '_'
			drawMan n = concat $ interspere "\n" [layer1, layer2, layer3, layer4, layer5]
				where	layer1			= "   |---|"
					layer2	| n > 0		= "   O   |"
						| otherwise	= "       |"
					layer3	| n > 3		= "  /|\  |"
						| n > 2		= "  /|   |"
						| n > 1		= "   |   |"
						| otherwise	= "       |"
					layer4	| n > 5		= "  / \  |"
						| n > 4		= "  /    |"
						| otherwise	= "       |"
					layer5			= "      / \"



-- Untyped

data Exp	= Var Ident
		| Lambda Ident Exp
		| Apply Exp Exp

-- Simple

data Exp	= Unit
		| Var Ident
		| Lambda Ident Type Exp
		| Apply Exp Exp

data Type	= Unit
		| Func Type Type

-- Polymorphic

data Exp	= Var Ident
		| Lambda Ident Type Exp
		| Apply Exp Exp
		| TLambda Ident Exp
		| TApply Exp Type

data Type	= TVar Ident
		| Forall Ident Type
		| Func Type Type

-- Second Order

data Exp	= Unit
		| Var Ident
		| Lambda Ident Type Exp
		| Apply Exp Exp

data Type	= Unit
		| Var Ident
		| Lambda Ident Kind Type
		| Apply Type Type

data Kind	= Unit
		| Func Kind Kind
		
-- F omega

data Exp	= Var Ident
		| Lambda Ident Type Exp
		| Lambda Ident Kind Exp
		| Apply Exp Exp
		| Apply Exp Type

data Type	= Arrow
		| TVar Ident
		| Lambda Ident Kind Type
		| Forall Ident Kind Type
		| Apply Type Type

data Kind	= Unit
		| Func Kind Kind

-- F omega + Ext

data Exp	= Pair
		| Inl
		| Inr
		| Unit
		| Var Ident
		| Lambda Ident Type Exp
		| TLambda Ident Kind Exp
		| Apply Exp Exp
		| TApply Exp Type

data Type	= Arrow
		| Cross
		| Union
		| Unit
		| TVar Ident
		| Lambda Ident Kind Type
		| Forall Ident Kind Type
		| Apply Type Type

data Kind	= Unit
		| Func Kind Kind


-- CC

data Exp	= Var Ident
		| Lambda Ident Type Exp
		| Lambda Ident Kind Exp
		| Apply Exp Exp
		| Apply Exp Type

data Type	= TVar Ident
		| Lambda Ident Kind Type
		| Forall Ident Kind Type
		| Forall Ident Type Type
		| Apply Type Type
		| Apply Type Exp

data Kind	= Unit
		| Func Kind Kind



Exists f = Ea. f a


Complex c = {
	polar : Real -> Real -> c,
	cartesian : Real -> Real -> c
}

Arith c = {
	add : c -> c -> c,
	mul : c -> c -> c
}

f : \/a. Complex a -> Arith a

g : (E ca. Complex c) -> (E c. Complex c * Arith c)
g {c, cpx} = {c, cpx * f [c] cpx}


let bool :: *
    bool = True : {} | False : {} in
let true, false :: bool
    true = True : {}
    false = False : {}
in false

(/\bool :: *.
	(\true :: bool. \false :: bool. 
		false)
	(True : {})
	(False : {})) 
[True : {} | False : {}]

let
	list :: * -> *
	list a = Mu l. Nil : {} | Cons : {Head : a, Tail : l}
in let
	nil :: \/a. list a
	nil [a] = Roll (Nil : {})
	
	cons :: \/a. a -> list a -> list a
	cons [a] x xs = Roll (Cons : {Head : x, Tail : xs})
in let	
	foldr :: \/a b. b -> (a -> b -> b) -> list a -> b
	foldr [a] [b] nil cons = fold
		where	rec fold xs = case (Unroll xs) of
				Nil : {} -> nil
				Cons : {Head : x, Tail : xs} -> cons x (fold xs)
	
	compose :: \/a b c. (b -> c) -> (a -> b) -> (a -> c)
	compose [b] [c] f [a] g x = f (g x)
	
in let
	append :: \/a. list a -> list a -> list a
	append [a] xs ys = foldr [a] [list a] ys (cons [a]) xs

	concat :: \/a. list (list a) -> list a
	concat [a] = foldr [list a] [list a] (nil [list a]) (append [list a])

	map :: \/a b. (a -> b) -> (list a -> list b)
	map [a] [b] f = foldr [a] [list b] (nil [list b]) (compose [a] [b] [list b -> list b] (cons [b]) f)

Eq :: \/k. k -> *
Eq <*> a = a -> a -> Bool
Eq <t -> s> f = \/a:t. Eq <t> a -> Eq <s> (f a)

Eq <* -> *> List
	= \/a:*. Eq <*> a -> Eq <*> (List a)
	= \/a:*. (a -> a -> Bool) -> (List a -> List a -> Bool)

(==) :: \/k. \/a:k. Eq <k> a
(==) <*> [1]   ()      ()      = True
(==) <*> [a+b] (Inl x) (Inl y) = (==) <*> [a] x y
(==) <*> [a+b] (Inr x) (Inr y) = (==) <*> [b] x y
(==) <*> [a+b] _       _       = False
(==) <*> [a*b] (w, x)  (y, z)  = (==) <*> [a] w y && (==) <*> [b] x z
(==) <t -> s> [f] [a] = \eqa -> (==) <s> [f a]



(==) [a] eqa = eq
	where	eq [] [] = True
		eq (x:xs) (y:ys) = eqa x y && eq xs ys 

Eq <* -> * -> *> F
	= \/a:*. Eq <*> a -> Eq <* -> *> (F a)
	= \/a:*. (a -> a -> Bool) -> (\/b:*. Eq <*> b -> Eq <*> (F a b))
	= \/a:*. (a -> a -> Bool) -> \/b:*. (b -> b -> Bool) -> F a b -> F a b -> Bool

Arrow <*> a b = a -> b
Arrow <t -> s> f = \/a b. Map <t> a b -> Map <s> (f a) (f b)

Arrow <* -> * -> *> F = \/a b. (a -> b) -> \/c d. (c -> d) -> F a c -> F b d




int[] nextRow(final int[] row) {
	final int[] next = new int[row.length + 1];
	
	for(int i = 1; i < row.length; i++)
		next[i] = row[i-1] + row[i];
	
	next[0] = 1;
	next[row.length] = 1;
	
	return next;
}

Iterator<int[]> pascal = iterate(nextRow, new int[] {1});


queens n = place [] {0 .. n} {}
	where	place qs {} diag = {qs}
		place qs pos diag = do
			let diag' = diag >>= \d -> {d-1, d+1}
			(p, pos') <- pick pos
			guard (not (p `member` diag'))
			place (p:qs) pos' (insert p diag')
	
			
--}

toMulti s = evalParser lex s >>= evalParser parse
notquite s = toMulti s >>= \exp -> evalStateT (steps exp) (Ident 0)
steps exp = first exp >>= second >>= andquart >>= andhalf >>= third >>= fourth >>= fifth >>= sixth
	where	first exp = return exp >>= return . curried >>= uniques >>= return . etaReduce . thunkify
		second exp = contify exp >>= normalize . inlineCont >>= return . linear . usage . inlineAlias
		andquart exp = return exp >>= return . restrict . free >>= lifted
		andhalf exps = concatMapM (uncurry closure) exps
--		andhalf exp = fresh >>= \main -> closure main exp
		third exps = do
			put (Ident 0)
			globals <- mapM (\(x, v) -> (x,) <$> fresh) exps
			let globalM = Data.Map.fromList globals
			values <- mapM (\(x, v) -> reuniq v globalM) exps
			return (zipWith (\(x, y) v -> (y, v)) globals values)
		fourth exps = concatMapM (\(x, v) -> lifting x v (Data.Map.fromList $ exps)) exps
		fifth exps = return $ fmap (\(x, v) -> (x, bruijn v)) exps
		sixth exps = return $ fmap (\(x, v) -> (x, geninst v)) exps

-- concatMapM :: (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs


ycomb = "\\f. (\\x.x x) (\\x.f (x x))"
self = "\\x. x x"






-- Currying
curried :: MultiExp -> SimpleExp
curried = foldMulti var lambda apply
	where	var = SVar
		lambda xs ce = foldr SLambda ce xs
		apply = foldl SApply

-- uniques :: SimpleExp -> StateT Ident Maybe UniqExp
uniques exp = runReaderT (fold exp) Data.Map.empty
	where	fold = foldSimple var lambda apply

		var x = do
			r <- Data.Map.lookup x <$> ask
			maybe mzero (return . UIdent) r

		lambda x fe = do
			y <- lift fresh
			ue <- local (Data.Map.insert x y) fe
			return (ULambda y ue)

		apply ff fx = UApply <$> ff <*> fx
				
	
thunkify :: UniqExp -> ThunkExp 
thunkify = foldUniq ident lambda apply
	where	ident x = HApply (HIdent x) []
		lambda x fe = HLambda [x] fe
		apply ff fx = HApply ff [HLambda [] fx]

{--
	[[ _ ]] :: a -> a
	[[ x ]] = x ()
	[[ \x -> e ]] = \x -> [[ e ]]
	[[ f e ]] = [[ f ]] (\() -> [[ e ]])
--}

contify = foldThunk ident lambda apply
	where	ident x = return (CLambda [] (CReturn CCurrent [CIdent x]))
	
		lambda xs fe = do
			CLambda [] body <- fe
			return (CLambda [] (CReturn CCurrent [CLambda xs body]))

		apply ff fxs = do
			(f:xs) <- sequence (ff:fxs)
			(g:ys) <- mapM (const fresh) (f:xs)
			return (CLambda [] (chain (f:xs) (g:ys) (app g ys)))

		chain vs xs body = foldr partial body (zip vs xs)
			where	partial (v, x) body = CApply v [] (CCont [x] body)
		
		app g ys = CApply (CIdent g) (fmap CIdent ys) CCurrent

{--
	[[ _ ]] :: a -> ((a -> b) -> b)
	[[ x ]] k = k x
	[[ \x -> e ]] k = k \x -> [[ e ]]
	[[ f x ]] k = [[ f ]] \g -> [[ x ]] \y -> g y k
--}

normalize exp = foldCCont lambda ident current cont apply ret exp >>= \(Right (x, v)) -> return v
	where	lambda xs fe = do
			x <- fresh
			e <- fe
			return (Right (x, KLambda xs e))
			
		ident x = return (Left x)
		
		current = return KCurrent
		cont xs fe = KCont xs <$> fe
		
		apply ff fxs fk = do
			k <- fk
			(f:xs) <- sequence (ff:fxs)
			let (vs, g:ys) = traverse (f:xs)
			return (lets vs (KApply g ys k))

		ret fk fxs = do
			k <- fk
			xs <- sequence fxs
			let (vs, ys) = traverse xs
			return (lets vs (KReturn k ys))
		
		traverse = foldr each ([], [])
			where	each (Left x)  (vs, xs) = (vs, x:xs)
				each (Right (x, v)) (vs, xs) = ((x, v):vs, x:xs)
		
		lets xvs body = foldr each body xvs
			where	each (x, v) body = KLet (KCont [x] body) v


lifted exp = evalStateT (foldV exp >>= fix) Data.Map.empty
	where	fix (Left v) = do
			main <- lift fresh
			modify (Data.Map.insert main v)
			Data.Map.toList <$> get
		fix (Right (NLambda free _ _)) = error $ "The whole AST cannot have free variables: " ++ show free
		
		foldV (NLambda free xs e) = do
			env <- get
			let localfr = Set.difference free (Data.Map.keysSet env)
			v <- NLambda localfr xs <$> foldB e
			return $ if (all (\x -> Data.Map.member x env) (Set.toList free))
				then	Left v
				else	Right v
		
		foldC NCurrent = return NCurrent
		foldC (NCont xs e) = NCont xs <$> foldB e
		
		foldB (NApply f xs k) = NApply f xs <$> foldC k
		foldB (NReturn k xs) = NReturn <$> foldC k <*> pure xs
		foldB (NLet k v) = do
			ev <- foldV v
			case ev of
				Left v -> case k of
					NCont [x] body -> modify (Data.Map.insert x v) >> foldB body
					NCurrent -> lift fresh >>= \x -> modify (Data.Map.insert x v) >> return (NReturn NCurrent [x])
				Right v -> NLet <$> foldC k <*> pure v 

free exp = evalWriter (fold exp)
	where	fold = foldCont lambda current cont apply klet ret
		lambda xs fe = do
			(e, fr) <- listen (censor (remove xs) fe)
			return (NLambda fr xs e)
		
		current = return NCurrent
		cont xs fe = NCont xs <$> censor (remove xs) fe
		
		apply f xs fk = do
			k <- fk
			tell (Set.fromList (f:xs))
			return (NApply f xs k)
			
		ret fk xs = do
			k <- fk
			tell (Set.fromList xs)
			return (NReturn k xs)
		
		klet fk fv = NLet <$> fk <*> fv
			
		remove xs = \s -> Set.difference s (Set.fromList xs)

restrict exp = runReader (fold exp) Set.empty
	where	fold = foldAnn lambda current cont apply nlet ret
		
		lambda free xs fe = NLambda <$> restrict free <*> pure xs <*> fe
		
		apply f xs fk = NApply f xs <$> fk (repeat False)
		ret fk xs = NReturn <$> fk (repeat False) <*> pure xs
		nlet fk fv = do
			v <- fv
			let NLambda free _ _ = v
			k <- fk [Set.null free]
			return (NLet k v)
			
		current gs = return NCurrent
		cont xs fe gs = NCont xs <$> local (addGlobals xs gs) fe
		
		restrict free = Set.difference free <$> ask
		isGlobal id = Set.member id <$> ask
		addGlobals xs gs = Set.union (Set.fromList (foldr filter [] (zip xs gs)))
			where	filter (x, g) rest | g = x : rest
						   | otherwise = rest


-- closure :: Var -> Annot -> State Var [(Var, Value)]
closure x exp = foldAnn lambda current cont apply nlet ret exp >>= fix
	where	fix (v, fr) = do
			label <- fresh
			return [(label, v), (x, RTuple (label:fr))]
	
		lambda free xs fe = do
			e <- fe
			let fr = Set.toList free
			this <- fresh
			return (RLambda (this:xs) (fetch this fr e), fr)

		fetch this free body = foldr (uncurry f) body (zip free [1..])
			where	f x i body = RDest (RCont [x] body) (RProj i this)
		
		current = return RCurrent
		cont xs fe = RCont xs <$> fe
		
		apply f xs fk = do
			k <- fk
			g <- fresh
			let pick body = (RDest (RCont [g] body) (RProj 0 f))
			return (pick (RDest k (RApply g (f:xs))))
		
		ret fk xs = RReturn <$> fk <*> pure xs
		
		nlet fk fv = do
			(v, fr) <- fv
			k <- fk
			label <- fresh
			let lam body = RCons (RCont [label] body) v
			return (lam (RCons k (RTuple (label:fr))))

{--
	[[ x ]] = x
	[[ \x -> e ]] = let free = FV(\x -> e) in (\fr x -> [[ e ]][free/fr.free], free)
	[[ f x ]] = let (g, fr) = [[ f ]] in g fr [[ x ]]

--}

-- Closure conversions duplicates the name of free variables in/out of the functions
reuniq exp = runReaderT (fold exp)
	where	fold = foldClos lambda tuple apply proj cons dest ret current cont
	
		lambda = abstract RLambda
		tuple xs = RTuple <$> getIdents xs

		apply f xs = RApply <$> getIdent f <*> getIdents xs
		proj i x = RProj i <$> getIdent x
		
		cons fk fv = RCons <$> fk <*> fv
		dest fk fe = RDest <$> fk <*> fe
		ret fk xs = RReturn <$> fk <*> getIdents xs
		
		current = return RCurrent
		cont = abstract RCont
		
		abstract abs xs fe = do
			ys <- makeFresh xs
			e <- local (addBindings xs ys) fe
			return (abs ys e)
			
		makeFresh xs = lift $ mapM (const fresh) xs
		addBindings xs ys = Data.Map.union (Data.Map.fromList (zip xs ys))
		getIdents = mapM getIdent
		getIdent x = do
			my <- Data.Map.lookup x <$> ask
			case my of
				Just y -> return y
				Nothing -> mzero


lifting x exp globals = evalStateT (fold exp >>= fix) Data.Map.empty
	where	fold = foldClos lambda tuple apply proj cons dest ret current cont
		fix (Left f) = modify (Data.Map.insert x f) >> (Data.Map.toList <$> get)
		fix (Right xs) = error $ "The whole AST cannot have free variables: " ++ show xs
	
		lambda xs fe = Left . LLambda xs <$> fe
		tuple xs = do
			return $ if (all (\x -> Data.Map.member x globals) xs)
				then Left (LTuple xs)
				else Right xs
		
		apply f xs = return (RApply f xs)
		proj i x = return (RProj i x)
		
		cons fk fv = do
			ev <- fv
			k <- fk
			(x, body) <- (case k of
				LCurrent -> lift fresh >>= \y -> return (y, LReturn LCurrent [y])
				LCont [y] e -> return (y, e))
			case ev of
				Left global -> do
					modify (Data.Map.insert x global)
					return body
				Right xs -> do
					let stores = foldr (\(y, i) body -> LAssign (LValue x i) y body) body (zip xs [0..])
					return (LAlloc (LCont [x] stores) (length xs))
		
		dest fk fe = LDest <$> fk <*> fe
		ret fk xs = LReturn <$> fk <*> pure xs
		
		current = return LCurrent
		cont xs fe = LCont xs <$> fe
		

bruijn = foldGlobal lambda tuple current cont alloc dest apply proj assign ret
	where	lambda xs fe = BLambda (length xs) (fe xs)
		tuple xs = BTuple xs

		current vars = BCurrent (length vars)
		cont xs fe vars = BCont (length xs) (fe (xs ++ vars))
		
		alloc fk n vars = BAlloc (fk vars) n
		dest fk fe vars = BDest (fk vars) (fe vars)
		
		apply f xs vars = BApply (var f vars) (fmap (`var` vars) xs)
		proj i x vars = BProj i (var x vars)
		
		assign (LValue x i) y fe vars = BAssign (BRef (var x vars) i) (var y vars) (fe vars)
		ret fk xs vars = BReturn (fk vars) (fmap (`var` vars) xs)
		
		
		var x vars = case (Data.List.elemIndex x vars) of
			Nothing -> BGlobal x
			Just i  -> BLocal i


data Decl	= Vector [Ident]
		| Block [Inst]
data Inst	= Malloc
 		| Push Nat
 		| Pop Nat
 		| Local Nat Regis
 		| Spill Regis Nat
 		| Return
 		| Const Nat Regis
 		| Label Ident Regis
 		| Load Indir Regis
 		| Move Regis Regis
 		| Store Regis Indir
 		| DynCall Regis
 		| Call Ident
data Indir = Indir Nat Regis

peephole (Push 1 : Spill r 0 : is) = "pushl " ++ show r
peephole (Local 0 r : Pop 1 : is) = "popl " ++ show r
peephole (Spill r1 n : Local m r2 : is) | n == m = "movl " ++ show r1 ++ ", " ++ show r2
peephole (Move r1 r2 : is) | r1 == r2 = ""
peephole (Call g : Pop n : is) = peephole (Pop n : Call g : is)
peephole (Call g : Return : []) = "jmp " ++ show g

geninst = foldBruijn lambda tuple current cont alloc dest apply proj assign ret
	where	lambda n fe = Block $ args n ++ fe
		tuple xs = Vector xs
		
		current t = [Pop t, Return]
		cont n fe = args n ++ fe
		
		alloc fk n = [Main.Const n (Regis 0), Malloc] ++ fk
		dest fk fe = fe ++ fk
		
		apply f xs = zipWith get xs regs ++ [get f (Regis 4), DynCall (Regis 4)]
		proj i x = [get x (Regis 0), Load (Indir i (Regis 0)) (Regis 0)]
		
		assign (BRef x i) y fe = [get x (Regis 0), get y (Regis 1), Store (Regis 1) (Indir i (Regis 0))] ++ fe
		ret fk xs = zipWith get xs regs ++ fk

		get (BLocal i) = Local i
		get (BGlobal x) = Label x
		
		args n = [Push n] ++ (take n regs >>= \(Regis r) -> [Spill (Regis r) r])
		regs = fmap Regis [0..]
		
instance Show Inst where
	show Malloc = "call __malloc__"
	show (Push n) = "subl $" ++ show (n * 4) ++ ", %esp"
	show (Pop n) = "addl $" ++ show (n * 4) ++ ", %esp"
	show (Local n r) = "movl " ++ show (n * 4) ++ "(%esp), " ++ show r
	show (Spill r n) = "movl " ++ show r ++ ", " ++ show (n * 4) ++ "(%esp)"
	show Return = "ret"
	show (Main.Const n r) = "movl $" ++ show n ++ ", " ++ show r
	show (Label g r) = "movl $" ++ show g ++ ", " ++ show r
	show (Load ind r) = "movl " ++ show ind ++ ", " ++ show r
	show (Move r1 r2) = "movl " ++ show r1 ++ ", " ++ show r2
	show (Store r ind) = "movl " ++ show r ++ ", " ++ show ind
	show (DynCall r) = "call *" ++ show r
	show (Call g) = "call " ++ show g


instance Show Regis where
	show (Regis r) = '%' : names !! r
		where	names = ["eax", "ebx", "ecx", "edx", "edi"] ++ repeat (error $ show r)

instance Show Indir where
	show (Indir i r) = show (i * 4) ++ "(" ++ show r ++ ")"


instance Show Decl where
 	show (Vector v) = ".int" ++ (v >>= \id -> ' ' : '$' : show id)
 	show (Block is) = is >>= (\i -> show i ++ "\n")
 








-- Optimization



etaReduce = foldThunk ident lambda apply
	where	ident = HIdent
		
		lambda [] (HApply t []) = t
		lambda xs e = HLambda xs e
		
		apply = HApply


inlineCont exp = foldV exp
	where	foldV (CLambda xs e) = CLambda xs (foldB e [])
		foldV (CIdent x) = CIdent x
		
		foldC CCurrent [] = CCurrent
		foldC CCurrent (k:ks) = foldC k ks
		foldC (CCont xs e) ks = CCont xs (foldB e ks)
		
		foldB (CApply (CLambda xs e) vs k) ks = CReturn (CCont xs (foldB e (k:ks))) (fmap foldV vs)
		foldB (CApply f vs k) ks = CApply (foldV f) (fmap foldV vs) (foldC k ks)
		foldB (CReturn k vs) ks = CReturn (foldC k ks) (fmap foldV vs)

inlineAlias exp = foldV exp Data.Map.empty
	where	foldV (KLambda xs e) env = KLambda xs (foldB e env)
		
		foldC KCurrent env = KCurrent
		foldC (KCont xs (KReturn KCurrent ys)) env | xs == ys = KCurrent
		foldC (KCont xs e) env = KCont xs (foldB e env)
		
		foldB (KApply f xs k) env = KApply (bind f env) (fmap (\x -> bind x env) xs) (foldC k env)
		foldB (KLet k v) env = KLet (foldC k env) (foldV v env)
		foldB (KReturn (KCont xs e) ys) env = foldB e (combine xs (fmap (\y -> bind y env) ys) env)
		foldB (KReturn k xs) env = KReturn k (fmap (\x -> bind x env) xs)
		
		combine xs ys env = Data.Map.union (Data.Map.fromList (zip xs ys)) env
		bind x env = maybe x id (Data.Map.lookup x env)

data DValue a	= DLambda [Ident] (DBlock a)
		deriving (Show)
data DCont a	= DCurrent
		| DCont [Ident] (DBlock a)
		deriving (Show)
data DBlock a	= DApply Ident [Ident] (DCont a)
		| DReturn (DCont a) [Ident]
		| DLet a (DCont a) (DValue a)
		deriving (Show)

usage :: KVal -> DValue (Int, Int, Int)
usage exp = evalWriter (foldV exp)
	where	foldV (KLambda [] e) = DLambda [] <$> foldB e
		foldV (KLambda xs e) = DLambda xs <$> censor (MapM . fmap shift . runMap) (foldB e)
		
		foldC KCurrent = return DCurrent
		foldC (KCont xs e) = DCont xs <$> foldB e
		
		foldB (KApply f xs k) = DApply <$> strict f <*> mapM nonstrict xs <*> foldC k
		foldB (KReturn k xs) = DReturn <$> foldC k <*> mapM nonstrict xs
		foldB (KLet k v) = listen (foldC k) >>= \(fk, uses) -> 
			case fk of
				DCurrent -> DLet (extract stuck) fk <$> foldV v
				DCont [x] e -> DLet (use x uses) fk <$> foldV v
		
		shift (a, b, c) = (mempty, mempty, a <> b <> c)
		extract (Sum a, Sum b, Sum c) = (a, b, c)
		none = extract mempty
		use x (MapM map) = maybe none extract (Data.Map.lookup x map)

		put x use = tell (MapM (Data.Map.singleton x use)) >> return x
		strict x = put x (Sum 1, mempty, mempty)
		nonstrict x = put x (mempty, Sum 1, mempty)
		stuck = (mempty, mempty, Sum 1)

linear exp = foldV exp Data.Map.empty
	where	foldV (DLambda xs e) env = KLambda xs (foldB e env [])
	
		foldC DCurrent env [] = KCurrent
		foldC DCurrent env (k:ks) = foldC k env ks
		foldC (DCont xs e) env ks = KCont xs (foldB e env ks)
		
		foldB (DApply f xs k) env ks =
			case (Data.Map.lookup f env) of
				Nothing -> KApply f xs (foldC k env ks)
				Just (DLambda ys e) -> KReturn (KCont ys (foldB e env (k:ks))) xs
		foldB (DReturn k xs) env ks = KReturn (foldC k env ks) xs
		foldB (DLet use k v) env ks | once use = let
							DCont [x] e = k in
							foldB e (Data.Map.insert x v env) ks
					    | otherwise = KLet (foldC k env ks) (foldV v env)

		once (n, 0, 0) = n < 2
		once _ = False