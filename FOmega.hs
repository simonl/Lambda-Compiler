import Parser
import Control.Applicative as App
import Data.Map as Map
import Data.Traversable as Trav
import Data.Set as Set
import Data.List as List
import Control.Monad.Reader as Read
import Control.Monad.Writer as Write hiding (Sum, Product)
import Control.Monad.State
import Control.Monad.Error
import Debug.Trace
import Data.Either
import qualified Data.Foldable





fromJust (Just x) = x

type Nat = Int

data Fix f
	= In { out :: f (Fix f) }

instance (Show (f (Fix f))) => Show (Fix f) where
	show (In x) = "(" ++ show x ++ ")" 

instance (Eq (f (Fix f))) => Eq (Fix f) where
	In x == In y = x == y

instance (Show w, Show a) => Show (Writer w a)

instance (Monoid w) => Applicative (Writer w) where
	pure = return
	(<*>) = ap

instance (Error e) => Applicative (Either e) where
	pure = return
	(<*>) = ap
	
instance Applicative (Reader r) where
	pure = return
	(<*>) = ap

instance (Monad m) => Applicative (ReaderT r m) where
	pure = return
	(<*>) = ap

fresh = do
	x <- get
	put (x+1)
	return x









compile str = do
	e <- parse str
	guard (checkScope e emptyScope)
	let e' = bruijn e emptyOrdScope
	(t, ce) <- typecheck e' Nothing emptyTypeEnv
	let v = eval t ce emptyEvalEnv
	let s = evalType Type t emptyEvalEnv
	return (s, v)











data Token v
	= LexVariable v
	| LexOpenParen
	| LexCloseParen
	| LexOpenSquare
	| LexCloseSquare
	| LexColon
	| LexLambda
	| LexTLambda
	| LexForall
	| LexArrow
	| LexStar
	| LexDot
	deriving (Show, Eq)

tokens :: Parser String -> Parser [Token String]
tokens ident = lexical token whiteSpace
	where	token	 =  onStr "->" LexArrow
			<|> onStr "/\\" LexTLambda
			<|> onStr "\\/" LexForall
			<|> onChr ':' LexColon
			<|> onChr '.' LexDot
			<|> onChr '*' LexStar
			<|> onChr '\\' LexLambda
			<|> onChr '(' LexOpenParen
			<|> onChr ')' LexCloseParen
			<|> onChr '[' LexOpenSquare
			<|> onChr ']' LexCloseSquare
			<|> (unamb <$> ident)
			
		unamb "forall" = LexForall
		unamb x = LexVariable x

identifier = (:) <$> lower <*> many letter


variableTok = do
	t <- item
	case t of 
		LexVariable x -> return x
		_ -> abort














	
type Ident = String

data PValue t k
	= PVariable Ident
	| PLambda Ident (Maybe (t k)) (PAnnot t k)
	| PLambdaT Ident (Maybe k) (PAnnot t k)
	| PParen (PAnnot t k)
	deriving (Show)

data PExpr t k
	= PApply (PValue t k) [Either (PValue t k) (t k)]
	deriving (Show)

data PAnnot t k
	= PAnnot (PExpr t k) (Maybe (t k))
	deriving (Show)

data PTValue k
	= PTParen (PTAnnot k)
	| PTVariable Ident
	| PTLambda Ident (Maybe k) (PTAnnot k)
	| PTForall Ident (Maybe k) (PTAnnot k)
	deriving (Show)

data PTApp k
	= PTApp (PTValue k) [PTValue k]
	deriving (Show)

data PTExpr k
	= PFunc [PTApp k] (PTApp k)
	deriving (Show)

data PTAnnot k
	= PTAnnot (PTExpr k) (Maybe k)
	deriving (Show)
	
data PKValue
	= PKType
	| PKParen PKExpr
	deriving (Show)
	
data PKExpr
	= PKFunc [PKValue] PKValue
	deriving (Show)



parseTerm prsT prsK = annotation <* end
	where	annotation = do
			e <- expression
			mt <- annot (prsT prsK)
			return (PAnnot e mt)
		
		expression = PApply <$> value <*> many (value <||> targ)

		targ = do
			single LexOpenSquare
			t <- prsT prsK
			single LexCloseSquare
			return t

		value	 =  variable
			<|> lambda
			<|> lambdaT
			<|> (PParen <$> inparen annotation)
		
		variable = PVariable <$> variableTok
		
		lambda = do
			single LexLambda
			x <- variableTok
			mt <- annot (prsT prsK)
			single LexDot
			e <- annotation
			return (PLambda x mt e)

		lambdaT = do
			single LexTLambda
			a <- variableTok
			mk <- annot prsK
			single LexDot
			e <- annotation
			return (PLambdaT a mk e)


parseType prsK = annotation
	where	annotation = do
			e <- expression
			mt <- annot prsK
			return (PTAnnot e mt)

		expression = PFunc <$> many (application <* single LexArrow) <*> application
		
		application = PTApp <$> value <*> many value

		value	 = variable
			<|> lambda
			<|> forall
			<|> (PTParen <$> inparen annotation)

		variable = PTVariable <$> variableTok
		
		lambda = do
			single LexLambda
			x <- variableTok
			mk <- annot prsK
			single LexDot
			e <- annotation
			return (PTLambda x mk e)

		forall = do
			single LexForall
			x <- variableTok
			mk <- annot prsK
			single LexDot
			e <- annotation
			return (PTForall x mk e)

parseKind = expression
	where	expression = PKFunc <$> many (value <* single LexArrow) <*> value
		
		value	 = (single LexStar >> return PKType)
			<|> (PKParen <$> inparen expression)


annot p = optional (single LexColon >> p)
inparen p = do
	single LexOpenParen
	v <- p
	single LexCloseParen
	return v

























data Expr bind v
	= Variable v
	| Let (bind v (Type bind v)) (Expr bind v) (Expr bind v)
	| LetT (bind v Kind) (Type bind v) (Expr bind v)
	| Lambda (bind v (Type bind v)) (Expr bind v)
	| LambdaT (bind v Kind) (Expr bind v)
	| Apply (Expr bind v) (Expr bind v)
	| ApplyT (Expr bind v) (Type bind v)
	| TypeAnnot (Expr bind v) (Type bind v)
deriving instance (Eq (bind v (Type bind v)), Eq (bind v Kind), Eq (Type bind v), Eq v) => Eq (Expr bind v)
deriving instance (Show (bind v (Type bind v)), Show (bind v Kind), Show (Type bind v), Show v) => Show (Expr bind v)
	
data Type bind v
	= Func (Type bind v) (Type bind v)
	| Forall (bind v Kind) (Type bind v)
	| TVariable v
	| TLambda (bind v Kind) (Type bind v)
	| TApply (Type bind v) (Type bind v)
	| KindAnnot (Type bind v) Kind
deriving instance (Eq (bind v Kind), Eq (Expr bind v), Eq v) => Eq (Type bind v)
deriving instance (Show (bind v Kind), Show (Expr bind v), Show v) => Show (Type bind v)

data Kind
	= Type
	| Arrow Kind Kind
	deriving (Eq, Show)

data Decl v ann
	= Decl v (Maybe ann)
	deriving (Eq, Show)

data Annot v ann
	= Annot ann
	| NoAnnot
	deriving (Eq, Show)

data Empty v ann
	= Empty
	deriving (Eq, Show)

data FAnnot v ann
	= FAnnot ann
	deriving (Eq, Show)
	


abstractTerm abst absk = annot
	where	annot (PAnnot pe Nothing) = expr pe
		annot (PAnnot pe (Just t)) = TypeAnnot (expr pe) (abst absk t)
		
		expr (PApply pf pxs) = foldl apply (value pf) (fmap abs pxs)
			where	apply f (Left v) = Apply f v
				apply f (Right t) = ApplyT f t
			
				abs (Left v) = Left (value v)
				abs (Right t) = Right (abst absk t)

		value (PVariable x) = Variable x
		value (PLambda x mt pe) = Lambda (Decl x (abst absk <$> mt)) (annot pe)
		value (PLambdaT x mk pe) = LambdaT (Decl x (absk <$> mk)) (annot pe)
		value (PParen pe) = annot pe

abstractType absk = annot
	where	annot (PTAnnot pe Nothing) = expr pe
		annot (PTAnnot pe (Just k)) = KindAnnot (expr pe) (absk k)
		
		expr (PFunc pvs pv) = foldr Func (app pv) (app <$> pvs)

		app (PTApp pv pvs) = foldl TApply (value pv) (value <$> pvs)

		value (PTParen pa) = annot pa
		value (PTVariable a) = TVariable a
		value (PTLambda x mk pe) = TLambda (Decl x (absk <$> mk)) (annot pe)
		value (PTForall x mk pe) = Forall (Decl x (absk <$> mk)) (annot pe)

abstractKind = expr
	where	expr (PKFunc pvs pv) = foldr Arrow (value pv) (value <$> pvs)
	
		value PKType = Type
		value (PKParen pe) = expr pe

abstract = abstractTerm abstractType abstractKind


parse = tokenize >=> structure >=> return . abstract
	where	tokenize = evalParser (tokens identifier)
		structure = evalParser (parseTerm parseType parseKind)


















emptyScope = (Set.empty, Set.empty)
putTermVar x (vs, ts) = (Set.insert x vs, ts)
putTypeVar a (vs, ts) = (vs, Set.insert a ts)
termVarInScope x (vs, ts) = Set.member x vs
typeVarInScope a (vs, ts) = Set.member a ts

checkTermScope checkT = fold
	where	fold (Variable v) = termVarInScope v <$> ask	
		fold (Lambda (Decl x ann) e) = (&&) <$> annot ann <*> local (putTermVar x) (fold e)
		fold (LambdaT (Decl a ann) e) = local (putTypeVar a) (fold e)
		fold (Apply f x) = (&&) <$> fold f <*> fold x
		fold (ApplyT f t) = (&&) <$> fold f <*> checkT t
		fold (TypeAnnot e t) = (&&) <$> fold e <*> checkT t

		annot Nothing = return True
		annot (Just t) = checkT t

checkTypeScope = fold
	where	fold (Func a b) = (&&) <$> fold a <*> fold b
		fold (Forall (Decl a mk) t) = local (putTypeVar a) (fold t)
		fold (TVariable a) = typeVarInScope a <$> ask
		fold (TLambda (Decl a mk) t) = local (putTypeVar a) (fold t)
		fold (TApply c t) = (&&) <$> fold c <*> fold t
		fold (KindAnnot t k) = fold t

checkScope = runReader . checkTermScope checkTypeScope


















emptyOrdScope = ([], [])
putTermName x (vs, ts) = (x:vs, ts)
putTypeName a (vs, ts) = (vs, a:ts)
termVarIndex x (vs, ts) = fromJust (elemIndex x vs)
typeVarIndex a (vs, ts) = fromJust (elemIndex a ts)

bruijnTerm brjT = fold
	where	fold (Variable x) = Variable . termVarIndex x <$> ask
		fold (Lambda (Decl x ann) e) = Lambda <$> annot brjT ann <*> local (putTermName x) (fold e)
		fold (LambdaT (Decl a ann) e) = LambdaT <$> annot return ann <*> local (putTypeName a) (fold e)
		fold (Apply f x) = Apply <$> fold f <*> fold x
		fold (ApplyT f t) = ApplyT <$> fold f <*> brjT t
		fold (TypeAnnot e t) = TypeAnnot <$> fold e <*> brjT t

		annot brj Nothing = return NoAnnot
		annot brj (Just t) = Annot <$> brj t

bruijnType = fold
	where	fold (Func a b) = Func <$> fold a <*> fold b
		fold (Forall (Decl a mk) t) = Forall <$> annot mk <*> local (putTypeName a) (fold t)
		fold (TVariable a) = TVariable . typeVarIndex a <$> ask
		fold (TLambda (Decl a mk) t) = TLambda <$> annot mk <*> local (putTypeName a) (fold t)
		fold (TApply c t) = TApply <$> fold c <*> fold t
		fold (KindAnnot t k) = KindAnnot <$> fold t <*> return k
		
		annot Nothing = return NoAnnot
		annot (Just k) = return (Annot k)

bruijn = runReader . bruijnTerm bruijnType















data CType
	= CFunc CType CType		-- type n ctx Type = Func : type n ctx Type * type n ctx Type
	| CForall Kind CType		-- type n ctx Type = Forall : (k:Kind) * type n ctx (Arrow k Type)
	| CTIndex Nat			-- type n ctx k = enum n
	| CTLambda CType		-- type n ctx (Arrow k h) = type (1+n) (k, ctx) h
	| CTApply Kind CType CType	-- type n ctx k = (h:Kind) * type n ctx (Arrow h k) * type n ctx h
	deriving (Eq, Show)

data CExpr
	= CIndex Nat			 -- expr r = nat
	| CLambda CExpr	 		 -- expr (Func a b) = expr b
	| CLambdaT CExpr		 -- expr (Forall k c) = (t:type k) -> expr (apply c t)
	| CApply CType CExpr CExpr	 -- expr r = (t:type Star) * expr (Func t r) * expr t
	| CApplyT Kind CType CExpr CType -- expr r = (k:Kind) * (c:type (Arrow k Star)) * expr (Forall k c) * (t:type k) * (r = apply c t)
	deriving (Eq, Show)




emptyTypeEnv = ([], [])
putType t (ts, ks) = (t:ts, ks)
putKind k (ts, ks) = (fmap (shift 1) ts, k:ks)
getType i (ts, ks) = ts !! i
getKind i (ts, ks) = ks !! i

inferType (Variable i) = do
	t <- getType i <$> ask
	return (t, CIndex i)
inferType (Lambda NoAnnot e) = mzero
inferType (Lambda (Annot t) e) = do
	a <- verifyType t Type
	(b, ce) <- local (putType a) (inferType e)
	return (CFunc a b, CLambda ce)
inferType (LambdaT NoAnnot e) = do
	(r, ce) <- local (putKind Type) (inferType e)
	return (CForall Type r, CLambdaT ce)
inferType (LambdaT (Annot k) e) = do
	(r, ce) <- local (putKind k) (inferType e)
	return (CForall k r, CLambdaT ce)
inferType (Apply f x) = do
	(CFunc a b, cf) <- inferType f
	cx <- checkType x a
	return (b, CApply a cf cx)
inferType (ApplyT f t) = do
	(CForall k e, cf) <- inferType f
	ct <- verifyType t k
	return (beta ct e, CApplyT k e cf ct)
inferType (TypeAnnot e t) = do
	ct <- verifyType t Type
	ce <- checkType e ct
	return (ct, ce)

checkType (Variable i) t = do
	s <- getType i <$> ask
	guard (t == s)
	return (CIndex i)
checkType (Lambda NoAnnot e) (CFunc a b) = do
	ce <- local (putType a) (checkType e b)
	return (CLambda ce)
checkType (Lambda (Annot t) e) (CFunc a b) = do
	ct <- verifyType t Type
	guard (ct == a)
	ce <- local (putType a) (checkType e b)
	return (CLambda ce)
checkType (Lambda annot e) t = mzero
checkType (LambdaT NoAnnot e) (CForall k t) = do
	ce <- local (putKind k) (checkType e t)
	return (CLambdaT ce)
checkType (LambdaT (Annot h) e) (CForall k t) = do
	guard (h == k)
	ce <- local (putKind k) (checkType e t)
	return (CLambdaT ce)
checkType (LambdaT annot e) t = mzero
checkType (Apply f x) b = do
	(a, cx) <- inferType x
	cf <- checkType f (CFunc a b)
	return (CApply a cf cx)
checkType (ApplyT f t) b = do
	(CForall k e, cf) <- inferType f
	ct <- verifyType t k
	guard (beta ct e == b)
	return (CApplyT k e cf ct)
checkType (TypeAnnot e t) s = do
	ct <- verifyType t Type
	guard (ct == s)
	checkType e s

inferKind (TVariable i) = do
	k <- getKind i <$> ask
	return (k, CTIndex i)
inferKind (Func a b) = do
	ca <- checkKind a Type
	cb <- checkKind b Type
	return (Type, CFunc ca cb)
inferKind (Forall NoAnnot t) = do
	ct <- local (putKind Type) (checkKind t Type)
	return (Type, CForall Type ct)
inferKind (Forall (Annot k) t) = do
	ct <- local (putKind k) (checkKind t Type)
	return (Type, CForall k ct)
inferKind (TLambda NoAnnot t) = do
	(h, ct) <- local (putKind Type) (inferKind t)
	return (Arrow Type h, CTLambda ct)
inferKind (TLambda (Annot k) t) = do
	(h, ct) <- local (putKind k) (inferKind t)
	return (Arrow k h, CTLambda ct)
inferKind (TApply f t) = do
	(Arrow k h, cf) <- inferKind f
	ct <- checkKind t k
	return (h, CTApply k cf ct)
inferKind (KindAnnot t k) = do
	ct <- checkKind t k
	return (k, ct)

checkKind (TVariable i) k = do
	h <- getKind i <$> ask
	guard (k == h)
	return (CTIndex i)
checkKind (Func a b) Type = do
	ca <- checkKind a Type
	cb <- checkKind b Type
	return (CFunc ca cb)
checkKind (Func a b) k = mzero
checkKind (Forall NoAnnot t) Type = do
	ct <- local (putKind Type) (checkKind t Type)
	return (CForall Type ct)
checkKind (Forall (Annot k) t) Type = do
	ct <- local (putKind k) (checkKind t Type)
	return (CForall k ct)
checkKind (Forall annot t) k = mzero
checkKind (TLambda NoAnnot t) (Arrow k h) = do
	ct <- local (putKind k) (checkKind t h)
	return (CTLambda ct)
checkKind (TLambda (Annot a) t) (Arrow k h) = do
	guard (a == k)
	ct <- local (putKind k) (checkKind t h)
	return (CTLambda ct)
checkKind (TLambda annot t) k = mzero
checkKind (TApply f t) h = do
	(k, ct) <- inferKind t
	cf <- checkKind f (Arrow k h)
	return (CTApply k cf ct)
checkKind (KindAnnot t k) h = do
	guard (k == h)
	checkKind t k

verifyType t k = do
	s <- checkKind t k
	return (normalize s)

typecheck e Nothing = runReaderT (inferType e)
typecheck e (Just t) = runReaderT (inferType (TypeAnnot e t))








normalize t = runReader (rec t) 0
	where	rec (CFunc a b) = CFunc <$> rec a <*> rec b
		rec (CForall k t) = CForall k <$> local (+1) (rec t)
		rec (CTIndex i) = do
			depth <- ask
			return $ case (i < depth) of
				True -> CTIndex i
				False -> CTIndex i
		rec (CTLambda t) = CTLambda <$> local (+1) (rec t)
		rec (CTApply k c t) = apply k <$> rec c <*> rec t

beta x t = runReader (rec t) 0
	where	rec (CFunc a b) = CFunc <$> rec a <*> rec b
		rec (CForall k t) = CForall k <$> local (+1) (rec t)
		rec (CTIndex i) = do
			depth <- ask
			return $ case (compare i depth) of
				LT -> CTIndex i
				EQ -> shift depth x
				GT -> CTIndex (i-1)
		rec (CTLambda t) = CTLambda <$> rec t
		rec (CTApply k f t) = CTApply k <$> rec f <*> rec t
		
shift amount t = runReader (rec t) 0
	where	rec (CFunc a b) = CFunc <$> rec a <*> rec b
		rec (CForall k t) = CForall k <$> local (+1) (rec t)
		rec (CTIndex i) = do
			depth <- ask
			return $ case (i < depth) of
				True -> CTIndex i
				False -> CTIndex (i+amount)
		rec (CTLambda t) = CTLambda <$> rec t
		rec (CTApply k f t) = CTApply k <$> rec f <*> rec t

apply k (CTLambda t) x = beta x t
apply k c x = CTApply k c x




{--

repr : (k:[]) -> k -> *
repr <*> a = Repr a
repr <s -> t> f = (a:s) -> repr s a -> repr t (f a)

--}





type Env = ([Kind], [TRepr], [TRepr], [Value])

data Value
	= Clos Env CExpr
	| ClosT Env CExpr
	deriving (Show)

data TRepr
	= RFunc TRepr TRepr
	| RForall Kind Env CType
	| RClos Env CType
	deriving (Show)

emptyEvalEnv = ([], [], [], [])
getValue i (ks, cs, ts, vs) = vs !! i
getCons i (ks, cs) = cs !! i
putValue t v (ks, cs, ts, vs) = (ks, cs, t:ts, v:vs)
putCons k c (ks, cs, ts, vs) = (k:ks, c:cs, ts, vs)


eval t (CIndex i) (ks, cs, ts, vs) = vs !! i
eval (CFunc a b) (CLambda e) env = Clos env e
eval (CForall k t) (CLambdaT e) env = ClosT env e
eval t (CApply s f x) env = applyV (evalType Type s env) t  (eval (CFunc s t) f env) (eval s x env)
eval t (CApplyT k e f s) env = applyT k t (eval (CForall k e) f env) (evalType k s env)

applyV s t (Clos (ks, cs, ts, vs) e) v = eval t e (ks, cs, s:ts, v:vs)

applyT k t (ClosT (ks, cs, ts, vs) e) c = eval t e (k:ks, c:cs, ts, vs)

evalType k (CTIndex i) (ks, cs, ts, vs) = cs !! i
evalType Type (CFunc a b) env = RFunc (evalType Type a env) (evalType Type b env)
evalType Type (CForall k e) env = RForall k env e
evalType (Arrow k h) (CTLambda e) env = RClos env e
evalType k (CTApply h c t) env = tApply h k (evalType (Arrow h k) c env) (evalType h t env)

tApply h k (RClos (ks, cs, ts, vs) e) c = evalType k e (h:ks, c:cs, ts, vs)

