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
import qualified Data.Array as Arr
import qualified Data.Foldable


index = (Arr.!)
array n f = Arr.array (0, n-1) [(i, f i) | i <- Arr.range (0, n-1)]
fromList xs = Arr.listArray (0, l-1) xs
	where	l = length xs

retry :: (Monad m) => m (Either e a) -> (e -> m ()) -> m a
retry try fail = do
	mv <- try
	case mv of
		Left err -> fail err >> retry try fail
		Right v -> return v


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
	
parse s = abstract <$> (evalParser tokens >=> evalParser parseTerm) s
parseNormalType = evalParser tokens >=> evalParser parseType >=> return . abstractType >=> return . (\e -> runReader e []) . bruijnTVars Map.empty

fresh = do
	x <- get
	put (x+1)
	return x

prompt p = do
	putStr p
	getLine

domain :: (Ord k) => Map k v -> Set k
domain = Set.fromList . Map.keys

showMap m = showL (Map.toList m)
	where	showL [] = ""
		showL (x:xs) = showField x ++ foldr (\f ls -> ", " ++ showField f ++ ls) "" xs
		showField (k, v) = show k ++ ":" ++ show v

maps f = Map.fromList . fmap (\x -> (x, f x)) . Set.toList

annot (In (Annot r a)) = a

annotate :: (Functor f) => (f a -> a) -> Fix f -> Fix (Annot f a)
annotate = Main.fold . annots
	where	annots g x = In (Annot x (g (fmap annot x)))


annotateM :: (Traversable f, Functor m, Monad m) => (f (m a) -> m a) -> Fix f -> m (Fix (Annot f a))
annotateM = Main.fold . annotsM
	where	annotsM g x = do
			a <- g (fmap (fmap annot) x)
			y <- Trav.sequence x
			return (In (Annot y a))

fold :: (Functor f) => (f a -> a) -> Fix f -> a
fold g = rec
	where	rec = g . fmap rec . out
	
unfold :: (Functor f) => (a -> f a) -> a -> Fix f
unfold g = rec
	where	rec = In . fmap rec . g


















data Token
	= LexKeyword String
	| LexVariable String
	| LexNumber Int
	| LexOpenCurly
	| LexCloseCurly
	| LexOpenParen
	| LexCloseParen
	| LexColon
	| LexOpenAngle
	| LexCloseAngle
	| LexOpenSquare
	| LexCloseSquare
	| LexLet
	| LexType
	| LexFix
	| LexIn
	| LexEqual
	| LexRoll
	| LexUnroll
	| LexRec
	| LexComma
	| LexLambda
	| LexTLambda
	| LexUnpack
	| LexUntag
	| LexFrom
	| LexForall
	| LexExists
	| LexSemiColon
	| LexBar
	| LexArrow
	| LexOpen
	| LexStar
	| LexAs
	| LexDot
	| LexCase
	| LexOf
	deriving (Show, Eq)



tokens = lexical token whiteSpace
	where	token	 =  onChr ':' LexColon
			<|> onChr '|' LexBar
			<|> onChr '.' LexDot
			<|> onChr '*' LexStar
			<|> onChr ',' LexComma
			<|> onChr '\\' LexLambda
			<|> onChr ';' LexSemiColon
			<|> onChr '{' LexOpenCurly
			<|> onChr '}' LexCloseCurly
			<|> onChr '[' LexOpenSquare
			<|> onChr ']' LexCloseSquare
			<|> onChr '(' LexOpenParen
			<|> onChr ')' LexCloseParen
			<|> onChr '=' LexEqual
			<|> onStr "->" LexArrow
			<|> onStr "/\\" LexTLambda
			<|> LexKeyword <$> keyword
			<|> unamb <$> identifier
			<|> LexNumber <$> number

		unamb "case" = LexCase
		unamb "open" = LexOpen
		unamb "as" = LexAs
		unamb "of" = LexOf
		unamb "forall" = LexForall
		unamb "exists" = LexExists
		unamb "unpack" = LexUnpack
		unamb "fix" = LexFix
		unamb "rec" = LexRec
		unamb "roll" = LexRoll
		unamb "unroll" = LexUnroll
		unamb "from" = LexFrom
		unamb "type" = LexType
		unamb "let" = LexLet
		unamb "in" = LexIn
		unamb "untag" = LexUntag
		unamb x = LexVariable x

		keyword = (:) <$> upper <*> many letter
		identifier = (:) <$> lower <*> many letter

keywordTok = do
	t <- item
	case t of 
		LexKeyword x -> return x
		_ -> abort

variableTok = do
	t <- item
	case t of 
		LexVariable x -> return x
		_ -> abort

numberTok = do
	t <- item
	case t of
		LexNumber n -> return n
		_ -> abort















	
{--

Fld := k : Exp
Val :=	\\ x (: Type)? . Exp
	{}
	x
	{ Fld (, Fld)* }
	/\\ a . Exp
	{ Type , Annot }
	< Ann >
	case Exp of { Cont (; Cont)* }
	\( Ann \)

Cont := k x (: Type)? . Exp

Proj :=	Val (. k)*

Arg :=	Proj
	[ Type ]
	
Exp :=	k Proj
	Proj Arg*
	roll Proj
	unroll Proj

Ann := Exp (: Type)?


TFld := k : Type
TVal :=	{}
	{ TFld (, TFld)* }
	\( Type \)
	forall x . Type
	exists x . Type
	fix x . Type

Type :=	k TVal (| k TVal)*
	(TVal ->)* TVal

Kind := (KVal ->)* KVal

KVal := \*
	\( Kind \)

--}

type Ident = String
type Keyword = String

data PField a = PField Keyword a

data PValue
	= PVariable Ident
	| PNumber Int
	| PKeyUnit Keyword
	| PLambda Ident (Maybe PTExpr) PAnnot
	| PRecur Ident (Maybe PTExpr) PAnnot
	| PRecord (Map Keyword PAnnot)
	| PPack PTExpr PAnnot
	| PTLambda Ident PAnnot
	| PCase PAnnot (Map Keyword (Ident, Maybe PTExpr, PAnnot))
	| PUnpack Ident Ident (Maybe PTExpr) PAnnot PAnnot
	| PParen PAnnot
	deriving (Show)

data PProj
	= PProject PValue [Keyword]
	deriving (Show)
	
data PExpr
	= PInject Keyword PProj
	| PRoll PProj
	| PUnroll PProj
	| PApply PProj [Either PTExpr PProj]
	deriving (Show)

data PAnnot
	= PAnnot PExpr (Maybe PTExpr)
	deriving (Show)
	
data PTValue
	= PProd (Map Keyword PTExpr)
	| PForall Ident PTExpr
	| PFix Ident PTExpr
	| PExists Ident PTExpr
	| PTVar Ident
	| PTParen PTExpr
	deriving (Show)

data PTExpr
	= PSum (Map Keyword PTValue)
	| PFunc [PTValue] PTValue
	deriving (Show)

	




between o c p = do
	single o
	v <- p
	single c
	return v

inparen = between LexOpenParen LexCloseParen

incurly = between LexOpenCurly LexCloseCurly

inangle = between LexOpenAngle LexCloseAngle

field p = do
	k <- keywordTok
	single LexColon
	v <- p 
	return (k, v)

recordOf p = do 
	fs <- incurly (sepBy LexComma (field p) <|> return [])
	return (Map.fromList fs)

tagged p = do
	k <- keywordTok
	v <- p <|> (return (PProd Map.empty))
	return (k, v)

parseTerm = annotation <* end
	where	annotation = do
			e <- expression
			mt <- optional (single LexColon >> parseType)
			return (PAnnot e mt)
		
		expression = rolling <|> unrolling <|> tagging <|> application
		
		rolling = single LexRoll *> (PRoll <$> proj)
		unrolling = single LexUnroll *> (PUnroll <$> proj)
		tagging = PInject <$> keywordTok <*> proj
		application = PApply <$> proj <*> many (typeArg <||> proj)
		
		proj = PProject <$> value <*> many (single LexDot >> keywordTok)
		typeArg = do
			single LexOpenSquare
			t <- parseType
			single LexCloseSquare
			return t

		value	 =  variable
			<|> (PKeyUnit <$> keywordTok)
			<|> lambda
			<|> tlambda
			<|> number
			<|> pack
			<|> recur
			<|> record
			<|> caseof
			<|> unpack
			<|> paren
		
		variable = PVariable <$> variableTok
		
		number = PNumber <$> numberTok
		
		lambda = do
			single LexLambda
			x <- variableTok
			mt <- optional (single LexColon >> parseType)
			single LexDot
			e <- annotation
			return (PLambda x mt e)
		
		tlambda = do
			single LexTLambda
			a <- variableTok
			single LexDot
			e <- annotation
			return (PTLambda a e)
		
		pack	= do
			single LexOpenCurly
			t <- parseType
			single LexComma
			e <- annotation
			single LexCloseCurly
			return (PPack t e)
		
		recur	= do
			single LexRec
			x <- variableTok
			mt <- optional (single LexColon >> parseType)
			single LexDot
			e <- annotation
			return (PRecur x mt e)
			
		record = PRecord <$> recordOf annotation
		
		caseof = do
			single LexCase
			e <- annotation
			single LexOf
			cs <- incurly (sepBy LexSemiColon caseClause)
			return (PCase e (Map.fromList cs))
			
		caseClause = do
			k <- keywordTok
			x <- variableTok
			mt <- optional (single LexColon >> parseType)
			single LexDot
			e <- annotation
			return (k, (x, mt, e))
		
		unpack = do
			single LexOpen
			e1 <- annotation
			single LexAs
			single LexOpenCurly
			a <- variableTok
			single LexComma
			x <- variableTok
			mt <- optional (single LexColon >> parseType)
			single LexCloseCurly
			single LexIn
			e2 <- annotation
			return (PUnpack a x mt e1 e2)
			
		paren = PParen <$> inparen annotation


parseType = expression
	where	expression = function <|> sum

		function = PFunc <$> many (value <* single LexArrow) <*> value
		
		sum = do
			ts <- sepBy LexBar (tagged value)
			return (PSum (Map.fromList ts))
		
		value	 = product
			<|> forall
			<|> exists
			<|> (PTVar <$> variableTok)
			<|> fixpoint
			<|> (PTParen <$> inparen expression)
		
		product = PProd <$> recordOf expression
		
		fixpoint = do
			single LexFix
			x <- variableTok
			single LexDot
			t <- expression
			return (PFix x t)
			
		forall = do
			single LexForall
			x <- variableTok
			single LexDot
			t <- expression
			return (PForall x t)
		
		exists = do
			single LexExists
			x <- variableTok
			single LexDot
			t <- expression
			return (PExists x t)
	


variable x = noAnnot (Variable x)
lambda b e = noAnnot (Lambda b e)
record es = noAnnot (Record es)
inject k e = noAnnot (Inject k e)
tlambda a e = noAnnot (TLambda a e)
recur b e = noAnnot (Recur b e)
pack t e = noAnnot (Pack t e)
apply f x = noAnnot (Apply f x)
roll e = noAnnot (Roll e)
unroll e = noAnnot (Unroll e)
tapply f t = noAnnot (TApply f t)
project v k = noAnnot (Project v k)
caseof s cs = noAnnot (Case s cs)
unpack a b e1 e2 = noAnnot (Unpack a b e1 e2)

noAnnot e = In (Annot e Nothing)
closing f a b = noAnnot (f a b)

abstract :: PAnnot -> Expr PType2 PBind2 Ident Keyword (Maybe (Fix (TypeVarRec Ident Keyword)))
abstract = annot
	where	annot (PAnnot pe t) = case (compatible mt1 mt2) of
					Left e -> error e
					Right mt -> In (Annot e mt)
			where	(In (Annot e mt2)) = expr pe
				mt1 = fmap abstractType t
		
		expr (PRoll p) = roll (proj p)
		expr (PUnroll p) = unroll (proj p)
		expr (PInject k p) = inject k (proj p)
		expr (PApply pf pxs) = foldl app (proj pf) (fmap arg pxs)
			where	app f = either (tapply f) (apply f)
				arg = either (Left . PType2 . abstractType) (Right . proj)

		proj (PProject pv ks) = foldl project (value pv) ks
		
		value (PVariable x) = variable x
		value (PNumber n) = noAnnot (Constant nat (iterate n))
			where	iterate 0 = zero
				iterate (n+1) = succ (iterate n)
				zero = In (RollVal (In (InjVal 1 (In (RecVal (Main.fromList []))))))				
				succ n = In (RollVal (In (InjVal 0 (In (RecVal (Main.fromList [n]))))))
				Just nat = parseNormalType "fix n. Zero | Succ { Pred : n }"
				
		value (PLambda x mt pe) = lambda (PBind2 x (abstractType <$> mt)) (annot pe)
		value (PTLambda a pe) = tlambda a (annot pe)
		value (PRecur x mt pe) = recur (PBind2 x (abstractType <$> mt)) (annot pe) 
		value (PKeyUnit k) = inject k (record Map.empty)
		value (PRecord pes) = record (fmap annot pes)
		value (PPack t pe) = pack (PType2 (abstractType t)) (annot pe)
		value (PCase ps pcs) = caseof (annot ps) (fmap (\(x, mt, e) -> (PBind2 x (abstractType <$> mt), annot e)) pcs)
		value (PUnpack a x mt e1 e2) = unpack a (PBind2 x (abstractType <$> mt)) (annot e1) (annot e2)
		value (PParen pe) = annot pe

abstractType = texp
	where	texp (PSum tvs) = sumT (fmap tval tvs)
		texp (PFunc as b) = foldr funcT (tval b) (fmap tval as)
		
		tval (PProd tes) = productT (fmap texp tes)
		tval (PTParen te) = texp te
		tval (PForall x te) = In (ForallV x (texp te))
		tval (PExists x te) = In (ExistsV x (texp te))
		tval (PFix x te) = In (FixV x (texp te))
		tval (PTVar x) = In (TVar x)
		
		noAnnot e = In (Annot e Nothing)

abstract2 :: PAnnot -> Fix (ExpRec PType2 PBind2 Ident Keyword)
abstract2 = annot
	where	annot (PAnnot pe Nothing) = expr pe
		annot (PAnnot pe (Just t)) = In $ TypeAnnot (expr pe) (PType2 (abstractType t))
		
		expr (PRoll p) = In $ Roll $ proj p
		expr (PUnroll p) = In $ Unroll $ proj p
		expr (PInject k p) = In $ Inject k $ proj p
		expr (PApply pf pxs) = foldl app (proj pf) (fmap arg pxs)
			where	app f = either (In . TApply f) (In . Apply f)
				arg = either (Left . PType2 . abstractType) (Right . proj)

		proj (PProject pv ks) = foldl (\e k -> In (Project e k)) (value pv) ks
		
		value (PVariable x) = In $ Variable x
		value (PNumber n) = In $ TypeAnnot (iterate n) (PType2 natType)
			where	iterate 0 = zero
				iterate (n+1) = succ (iterate n)
				zero = In $ Roll $ In $ Inject "Zero" (In $ Record Map.empty)		
				succ n = In $ Roll $ In $ Inject "Succ" (In $ Record (Map.singleton "Pred" n))
				

		value (PLambda x mt pe) = In $ Lambda (PBind2 x (abstractType <$> mt)) (annot pe)
		value (PTLambda a pe) = In $ TLambda a (annot pe)
		value (PKeyUnit k) = In $ Inject k $ In $ Record Map.empty
		value (PRecord pes) = In $ Record (fmap annot pes)
		value (PPack t pe) = In $ Pack (PType2 (abstractType t)) (annot pe)
		value (PCase ps pcs) = In $ Case (annot ps) (fmap (\(x, mt, e) -> (PBind2 x (abstractType <$> mt), annot e)) pcs)
		value (PUnpack a x mt e1 e2) = In $ Unpack a (PBind2 x (abstractType <$> mt)) (annot e1) (annot e2)
		value (PParen pe) = annot pe

(natType, listType, typeType) = (fixed nat, fixed . list, fixed typeT)
	where	sum ks ts = In (SumV (Map.fromList (zip ks ts)))
		product ks ts = In (ProductV (Map.fromList (zip ks ts)))
		fix v t = In (FixV v t)
		unit = product [] []
		var x = In (TVar x) 
		
		nat r = sum ["Zero", "Succ"] [unit, product ["Pred"] [r]]
		list t r = sum ["Nil", "Cons"] [unit, product ["Head", "Tail"] [t, r]]
		typeT r = sum ["Product", "Sum", "Func", "Forall", "Exists", "TIndex", "Fix"]
			[listType r,
			listType r,
			product ["From", "To"] [r, r],
			product ["Body"] [r],
			product ["Body"] [r],
			natType,
			product ["Body"] [r]]
	
		fixed f = fix "r" (f (var "r"))


compatible Nothing Nothing = return Nothing
compatible Nothing (Just t) = return (Just t)
compatible (Just t) Nothing = return (Just t)
compatible (Just s) (Just t)	| s == t = return (Just s)
				| otherwise = Left ("Type mismatch : " ++ show s ++ " != " ++ show t)

match t Nothing = True
match t (Just s) = s == t












instance Error (TypeError v k) where
	noMsg = TypeError
	strMsg s = TypeError

data TypeError v k
	= TypeError
	deriving (Show)

typecheck2 :: Fix (ExpRec PType PBind Ident Keyword) -> Either (TypeError Ident Keyword) (Type Keyword)
typecheck2 e = runReaderT (typeof e Nothing) (Map.empty, [])
	where	typeof (In e) exp =  expr e exp {-- do
			(ce, ct) <- expr e exp
			return (In (Annot ce ct))
		--}

		expr (Variable x) Nothing = (! x) <$> types
		expr (Variable x) (Just exp) = do
			t <- (! x) <$> types 
			guard (t == exp) TypeError
			return t
		
		expr (Lambda (PBind x Nothing) e) Nothing = throwError TypeError
		expr (Lambda (PBind x (Just t)) e) Nothing = do
			In Type <- kindof t
			let annot = normalize t
			ret <- local (addType x annot) (typeof e Nothing)
			return (In (Func annot ret))
		expr (Lambda (PBind x Nothing) e) (Just exp) = do
			In (Func a b) <- return exp
			_ <- local (addType x a) (typeof e (Just b))
			return exp
		expr (Lambda (PBind x (Just t)) e) (Just exp) = do
			In (Func a b) <- return exp
			In Type <- kindof t
			let annot = normalize t
			guard (a == annot) TypeError
			_ <- local (addType x a) (typeof e (Just b))
			return exp
		
		expr (TLambda a e) Nothing = do
			ret <- local (addKind (In Type)) (typeof e Nothing)
			return (In (Forall ret))
		expr (TLambda a e) (Just exp) = do
			In (Forall t) <- return exp
			_ <- local (addKind (In Type)) (typeof e (Just t))
			return exp
		
		expr (Record es) Nothing = do
			ts <- Trav.mapM (\e -> typeof e Nothing) es
			return (In (Product ts))
		expr (Record es) (Just exp) = do
			In (Product ts) <- return exp
			guard (Map.keys es == Map.keys ts) TypeError
			_ <- Trav.sequence (Map.mapWithKey (\k e -> typeof e (Just (ts ! k))) es)
			return exp
		
		expr (Pack t e) Nothing = throwError TypeError
		expr (Pack (PType t) e) (Just exp) = do
			In (Exists te) <- return exp
			In Type <- kindof t
			let abs = beta (normalize t) te
			_ <- typeof e (Just abs)
			return exp			
			
		expr (Inject k e) Nothing = throwError TypeError
		expr (Inject k e) (Just exp) = do
			In (Sum ts) <- return exp
			guard (Map.member k ts) TypeError
			_ <- typeof e (Just (ts ! k))
			return exp
		
		expr (Roll e) Nothing = throwError TypeError
		expr (Roll e) (Just exp) = do
			In (Fix te) <- return exp
			let unrolled = beta (In (Fix te)) te
			_ <- typeof e (Just unrolled)
			return exp
		
		expr (Apply f x) Nothing = do
			In (Func a b) <- typeof f Nothing
			_ <- typeof x (Just a)
			return b
		expr (Apply f x) (Just exp) = do
			a <- typeof x Nothing
			_ <- typeof f (Just (In (Func a exp)))
			return exp
		
		expr (TApply f (PType t)) Nothing = do
			In Type <- kindof t
			let arg = normalize t
			In (Forall te) <- typeof f Nothing
			return (beta arg te)
		expr (TApply f (PType t)) (Just exp) = do
			In Type <- kindof t
			let arg = normalize t
			In (Forall te) <- typeof f Nothing
			guard (exp == beta arg te) TypeError
			return exp
			
		expr (Project e k) Nothing = do
			In (Product ts) <- typeof e Nothing
			guard (Map.member k ts) TypeError
			return (ts ! k)
		expr (Project e k) (Just exp) = do
			In (Product ts) <- typeof e Nothing
			guard (Map.member k ts) TypeError
			guard (exp == ts ! k) TypeError
			return exp
		
		expr (Unpack a bind pk e) Nothing = do
			In (Exists te) <- typeof pk Nothing
			In (Forall (In (Func arg ret))) <- typeof (In (TLambda a (In (Lambda bind e)))) Nothing
			guard (te == arg) TypeError
			guard (noEscape ret) TypeError
			return (shift (-1) ret)
		expr (Unpack a bind pk e) (Just exp) = do
			In (Exists te) <- typeof pk Nothing
			let annot = PType (In (Func te (shift 1 exp)))
			let cont = In (TLambda a (In (TypeAnnot (In (Lambda bind e)) annot)))
			_ <- typeof cont Nothing
			return exp
		
		expr (Case e cs) Nothing = do
			In (Sum ts) <- typeof e Nothing
			guard (Map.keys ts == Map.keys cs) TypeError
			rs <- Trav.sequence (Map.mapWithKey (\k c -> cont c (ts ! k) Nothing) cs)
			(r:_) <- return (Map.elems rs)
			guard (all (== r) rs) TypeError
			return r
		expr (Case e cs) (Just exp) = do
			In (Sum ts) <- typeof e Nothing
			guard (Map.keys ts == Map.keys cs) TypeError
			rs <- Trav.sequence (Map.mapWithKey (\k c -> cont c (ts ! k) (Just exp)) cs)
			guard (all (== exp) rs) TypeError
			return exp
		
		expr (Unroll e) Nothing = do
			In (Fix te) <- typeof e Nothing
			let unrolled = beta (In (Fix te)) te
			return unrolled
		expr (Unroll e) (Just exp) = do
			In (Fix te) <- typeof e Nothing
			let unrolled = beta (In (Fix te)) te
			guard (exp == unrolled) TypeError
			return exp
		
		expr (TypeAnnot e (PType t)) Nothing = do
			In Type <- kindof t
			let annot = normalize t
			_ <- typeof e (Just annot)
			return annot
		expr (TypeAnnot e (PType t)) (Just exp) = do
			In Type <- kindof t
			let annot = normalize t
			guard (annot == exp) TypeError
			_ <- typeof e (Just exp)
			return exp
		
		cont (PBind x mannot, e) t mexp = do
			guard (match t mannot) TypeError
			local (addType x t) (typeof e mexp)
		
		match t Nothing = True
		match t (Just s) = s == t
		




		kindof (In t) = texp t
		
		texp (TIndex i) = (!! i) <$> kinds
		texp (Func a b) = do
			In Type <- kindof a
			In Type <- kindof b
			return (In Type)
		texp (Sum ts) = do
			ks <- Trav.mapM kindof ts
			guard (all (== In Type) ks) TypeError
			return (In Type)
		texp (Product ts) = do
			ks <- Trav.mapM kindof ts
			guard (all (== In Type) ks) TypeError
			return (In Type)
		texp (Fix r) = do
			In Type <- local (addKind (In Type)) (kindof r)
			return (In Type)
		texp (Forall r) = do
			In Type <- local (addKind (In Type)) (kindof r)
			return (In Type)
		texp (Exists r) = do
			In Type <- local (addKind (In Type)) (kindof r)
			return (In Type)
		texp (LambdaT r) = do
			k <- local (addKind (In Type)) (kindof r)
			return (In (ArrowK (In Type) k))
		texp (ApplyT c t) = do
			In (ArrowK a b) <- kindof c
			c <- kindof t
			guard (a == c) TypeError
			return b
		



		all p = Map.fold ((&&) . p) True
		guard True _ = return ()
		guard False err = throwError err
		
		types = fst <$> ask
		kinds = snd <$> ask

		addType x t (ts, ks) = (Map.insert x t ts, ks)
		addKind k (ts, ks) = (fmap (shift 1) ts, k:ks)





data ExpRec typ bind var key rec
	= Variable var
	| Recur (bind var key) rec
	| Lambda (bind var key) rec
	| TLambda var rec
	| Record (Map key rec)
	| Pack (typ var key) rec
	| Inject key rec
	| Roll rec
	| Apply rec rec
	| TApply rec (typ var key)
	| Project rec key
	| Unpack var (bind var key) rec rec
	| Case rec (Map key (bind var key, rec))
	| Unroll rec
	| TypeAnnot rec (typ var key)
	| Constant (Type key) (Fix (ValueRec key))

instance (Show (typ var key), Show (bind var key), Show var, Show key, Show rec) => Show (ExpRec typ bind var key rec) where
	show (Variable x) = show x
	show (Recur b e) = "rec " ++ show b ++ ". " ++ show e
	show (Lambda b e) = "\\" ++ show b ++ ". " ++ show e
	show (TLambda x e) = "/\\" ++ show x ++ ". " ++ show e
	show (Record fs) = "{" ++ showMap fs ++ "}"
	show (Pack t e) = "{" ++ show t ++ ", " ++ show e ++ "}"
	show (Inject k e) = "<" ++ show k ++ ":" ++ show e ++ ">"
	show (Roll e) = "roll " ++ show e
	show (Apply f x) = show f ++ " " ++ show x
	show (TApply f t) = show f ++ " [" ++ show t ++ "]"
	show (Project e k) = show e ++ "." ++ show k
	show (Unpack a b p e) = "unpack {" ++ show a ++ ", " ++ show b ++ "} = " ++ show p ++ " in " ++ show e
	show (Case e cs) = "case " ++ show e ++ " of {" ++ showMap cs ++ "}"
	show (Unroll e) = "unroll " ++ show e
	show (TypeAnnot e t) = show e ++ " : " ++ show t
	show (Constant t v) = show v


data PBind v k = PBind v (Maybe (Type k))	deriving (Show)

data Annot f a r = Annot (f r) a	deriving (Show)

type Expr typ bind var key ann = Fix (Annot (ExpRec typ bind var key) ann)


data TypeRec k r
	= Product (Map k r)
	| Sum (Map k r)
	| Func r r
	| Forall r
	| Exists r
	| TIndex Nat
	| Fix r
	| LambdaT r
	| ApplyT r r
	deriving (Eq)



type Type k = Fix (TypeRec k)

sumT = In . SumV
productT = In . ProductV
funcT a b = In (FuncV a b)

data Decl v k = Decl v	deriving (Show)

data PType v k = PType (Type k)	deriving (Show)

	
instance (Show k, Show r) => Show (TypeRec k r) where
	show (Product fs) = "{" ++ showMap fs ++ "}"
	show (Sum fs) = "<" ++ showMap fs ++ ">"
	show (Func a b) = show a ++ " -> " ++ show b
	show (Forall t) = "forall " ++ show t
	show (Exists t) = "exists " ++ show t
	show (Fix t) = "fix " ++ show t
	show (TIndex i) = show i
	show (LambdaT t) = "\\" ++ show t
	show (ApplyT c t) = show c ++ " " ++ show t
	
data KindRec r
	= Type
	| ArrowK r r
	deriving (Eq, Show)

type Kind = Fix KindRec













data TypeVarRec v k r
	= ProductV (Map k r)
	| SumV (Map k r)
	| FuncV r r
	| ForallV v r
	| ExistsV v r
	| FixV v r
	| TVar v
	| LambdaV v r
	| ApplyV r r
	deriving (Show, Eq)


data PType2 v k = PType2 (Fix (TypeVarRec v k))			deriving (Show)
data PBind2 v k = PBind2 v (Maybe (Fix (TypeVarRec v k)))	deriving (Show, Eq)



bruijnTypes tsyn e = runReader (fold e) []
	where	fold (In a) = In <$> annot a
	
		annot (Annot e mt) = Annot <$> expr e <*> inMaybe bruijnType mt
		
		expr (Variable x) = return (Variable x)
		expr (Record es) = Record <$> Trav.sequence (fmap fold es)
		expr (Inject k e) = Inject k <$> fold e
		expr (Lambda b e) = Lambda <$> inBind b <*> fold e
		expr (Recur b e) = Recur <$> inBind b <*> fold e
		expr (TLambda a e) = TLambda a <$> local (a:) (fold e)
		expr (Pack t e) = Pack <$> inType bruijnType t <*> fold e
		expr (Roll e) = Roll <$> fold e
		expr (Apply f x) = Apply <$> fold f <*> fold x
		expr (Project e k) = Project <$> fold e <*> pure k
		expr (Case e cs) = Case <$> fold e <*> Trav.sequence (fmap cont cs)
		expr (TApply f t) = TApply <$> fold f <*> inType bruijnType t
		expr (Unpack a b p e) = Unpack a <$> inBind b <*> fold p <*> local (a:) (fold e)
		expr (Unroll e) = Unroll <$> fold e
		expr (Constant t v) = return (Constant t v)
		
		cont (b, e) = (,) <$> inBind b <*> fold e
		
		inMaybe f Nothing = return Nothing
		inMaybe f (Just x) = Just <$> f x

		inType f (PType2 t) = PType <$> f t

		inBind (PBind2 x mt) = PBind x <$> inMaybe bruijnType mt
		
		bruijnType = bruijnTVars tsyn

bruijnTVars :: Map String (Type k) -> Fix (TypeVarRec String k) -> Reader [String] (Type k)
bruijnTVars tsyn = foldt
	where	foldt (In t) = In <$> texp t
	
		texp (TVar a) = do
			mi <- elemIndex a <$> ask
			return $ maybe (out (tsyn ! a)) TIndex mi
		texp (ProductV ts) = Product <$> Trav.sequence (fmap foldt ts)
		texp (SumV ts) = Sum <$> Trav.sequence (fmap foldt ts)
		texp (FuncV a b) = Func <$> foldt a <*> foldt b
		texp (ForallV a t) = Forall <$> local (a:) (foldt t)
		texp (ExistsV a t) = Exists <$> local (a:) (foldt t)
		texp (FixV a t) = Fix <$> local (a:) (foldt t)
		texp (LambdaV a t) = LambdaT <$> local (a:) (foldt t)
		texp (ApplyV c t) = ApplyT <$> foldt c <*> foldt t


beta t = mapLevels $ \i depth -> case (compare i depth) of
			GT -> TIndex (i - 1)
			EQ -> out $ shift depth t
			LT -> TIndex i
			
shift n = mapLevels $ \i depth -> case (compare i depth) of
			LT -> TIndex i
			_  -> TIndex (i + n)

noEscape = levels id allMap allMap id id id (&&) id (&&) (/=)
	where	allMap = Map.fold (&&) True
	
mapLevels = levels In Product Sum Forall Exists LambdaT ApplyT Fix Func

levels fix product sum forall exists lambda apply fixt func index e = runReader (fold e) 0
	where	fold (In t) = fix <$> expr t
	
		expr (TIndex i) = index i <$> ask
		expr (Forall t) = forall <$> local (1+) (fold t)
		expr (Exists t) = exists <$> local (1+) (fold t)
		expr (Fix t) = fixt <$> local (1+) (fold t)
		expr (Func a b) = func <$> fold a <*> fold b
		expr (Sum ts) = sum <$> Trav.sequence (fmap fold ts)
		expr (Product ts) = product <$> Trav.sequence (fmap fold ts)
		expr (LambdaT t) = lambda <$> local (1+) (fold t)
		expr (ApplyT c t) = apply <$> fold c <*> fold t

normalize (In t) = In (fold t)
	where	fold (TIndex i) = TIndex i
		fold (Forall t) = Forall (normalize t)
		fold (Exists t) = Exists (normalize t)
		fold (Fix t) = Fix (normalize t)
		fold (Func a b) = Func (normalize a) (normalize b)
		fold (Sum ts) = Sum (fmap normalize ts)
		fold (Product ts) = Product (fmap normalize ts)
		fold (LambdaT t) = LambdaT (normalize t)
		fold (ApplyT c t) = apply (normalize c) (normalize t)
	
		apply (In (LambdaT t)) v = out $ normalize (beta v t)
		apply c v = ApplyT c v





wellScoped :: (Ord v) => (Set v, Set v) -> Expr PType2 PBind2 v k (Maybe (Fix (TypeVarRec v k))) -> Bool
wellScoped scope e = runReader (fold e) scope
	where	fold (In ann) = annot ann
	
		annot (Annot e mt) = (&&) <$> exp e <*> annType mt
	
		exp (Variable x) = Set.member x . fst <$> ask
		exp (Lambda b e) = (&&) <$> annType (bindType b) <*> local (addVal b) (fold e)
		exp (Recur b e) = (&&) <$> annType (bindType b) <*> local (addVal b) (fold e)
		exp (TLambda a e) = local (addType a) (fold e)
		exp (Record fs) = allMap <$> Trav.sequence (fmap fold fs)
		exp (Pack t e) = (&&) <$> inType foldt t <*> fold e
		exp (Inject k e) = fold e
		exp (Roll e) = fold e
		exp (Apply f x) = (&&) <$> fold f <*> fold x
		exp (TApply f t) = (&&) <$> fold f <*> inType foldt t
		exp (Project e k) = fold e
		exp (Unpack a b p e) = (&&) <$> fold p <*> local (addType a) we
			where	we = (&&) <$> annType (bindType b) <*> local (addVal b) (fold e)
		exp (Case e cs) = (&&) <$> fold e <*> (allMap <$> Trav.sequence (fmap cont cs))
		exp (Unroll e) = fold e
		exp (Constant t v) = return True

		cont (b, e) = local (addVal b) (fold e)
		
		allMap = Map.fold (&&) True
		
		bindVar (PBind2 x _) = x
		bindType (PBind2 x t) = t
		
		addVal b (vs, ts) = (Set.insert (bindVar b) vs, ts)
		addType a (vs, ts) = (vs, Set.insert a ts)

		annType = maybe (return True) foldt
		inType f (PType2 t) = f t
		
		foldt t = ask >>= \(_, ts) -> return (runReader (wellScopedType t) ts)

wellScopedType = foldt
	where	foldt (In t) = typ t

		typ (ProductV ts) = allMap <$> Trav.sequence (fmap foldt ts)
		typ (SumV ts) = allMap <$> Trav.sequence (fmap foldt ts)
		typ (FuncV a b) = (&&) <$> foldt a <*> foldt b
		typ (ForallV a t) = local (addType a) (foldt t)
		typ (ExistsV a t) = local (addType a) (foldt t)
		typ (FixV a t) = local (addType a) (foldt t)
		typ (LambdaV a t) = local (addType a) (foldt t)
		typ (ApplyV c t) = (&&) <$> foldt c <*> foldt t
		typ (TVar a) = Set.member a <$> ask

		addType = Set.insert
		allMap = Map.fold (&&) True







	

typecheck :: (Ord k, Show k, Show var, Ord var) =>
     Map var (Type k)
     -> Fix (Annot (ExpRec PType PBind var k) (Maybe (Type k)))
     -> Either String (Fix (Annot (ExpRec PType Decl var k) (Type k)))

typecheck env e = fst <$> runReaderT (fold e Nothing) env
	where	fold (In a) exp = do
			(ca, ct) <- annot a exp
			return (In ca, ct)
		
		mismatch :: (Show k) => Type k -> Type k -> String
		mismatch t s = "Type mismatch: " ++ show t ++ " != " ++ show s
		fieldMismatch fs ts = "Field names mismatch: " ++ show (Map.keys fs) ++ " != " ++ show (Map.keys ts)
		tagMismatch t ts = "Tag name mismatch: " ++ show t ++ " is not in " ++ show (Map.keys ts)
		fieldAccess k ts = "Field access error: " ++ show k ++ " is not in " ++ show (Map.keys ts)
		notExhaust ts cs = "Not exhaustive case: " ++ show (Map.keys ts) ++ " does not match " ++ show (Map.keys cs)
		caseReturnMismatch cts = "Branch return types mismatch: " ++ show cts
		existEscapes t = "Existential type exits scope: " ++ show t

		annot (Annot e t) exp = do
			mt <- lift (compatible t exp)
--			trace ("\t" ++ show e ++ " :? " ++ show mt) (return ())
			(ce, ct) <- expr e mt
			return (Annot ce ct, ct)
		
		expr (Variable x) exp = do
			t <- (! x) <$> ask
			guard (match t exp) (mismatch t (fromJust exp))
			return (Variable x, t)
	
		expr (Constant t v) Nothing = return (Constant t v, t)
		expr (Constant t v) (Just exp) = do
			guard (t == exp) (mismatch t exp)
			return (Constant t v, t)
			
		expr (Recur (PBind x (Just t)) e) Nothing = do
			(ce, ct) <- local (Map.insert x t) (fold e (Just t))
			return (Recur (Decl x) ce, t)
		expr (Recur (PBind x (Just t)) e) (Just exp) = do
			guard (t == exp) (mismatch t exp)
			(ce, ct) <- local (Map.insert x t) (fold e (Just t))
			return (Recur (Decl x) ce, t)
		expr (Recur (PBind x Nothing) e) (Just exp) = do
			(ce, ct) <- local (Map.insert x exp) (fold e (Just exp))
			return (Recur (Decl x) ce, exp)

		expr (Lambda (PBind x (Just t)) e) Nothing = do
			(ce, ct) <- local (Map.insert x t) (fold e Nothing)
			return (Lambda (Decl x) ce, In (Func t ct))
		expr (Lambda (PBind x mt) e) (Just t) = do
			In (Func a b) <- return t
			guard (match a mt) (mismatch a (fromJust mt))
			(ce, ct) <- local (Map.insert x a) (fold e (Just b))
			return (Lambda (Decl x) ce, t)

		expr (TLambda a e) Nothing = do
			(ce, te) <- local (fmap (shift 1)) (fold e Nothing)
			return (TLambda a ce, In (Forall te))
		expr (TLambda a e) (Just exp) = do
			In (Forall te) <- return exp
			(ce, _) <- local (fmap (shift 1)) (fold e (Just te))
			return (TLambda a ce, exp)

		expr (Pack t e) Nothing = lift (Left "Cannot pack")
		expr (Pack (PType t) e) (Just exp) = do
			In (Exists te) <- return exp
			(ce, _) <- fold e (Just (beta t te))
			return (Pack (PType t) ce, exp)

		expr (Record fs) Nothing = do
			mcs <- Trav.sequence (fmap (\f -> fold f Nothing) fs)
			return (Record (fmap fst mcs), In (Product (fmap snd mcs)))
		expr (Record fs) (Just t) = do
			In (Product ts) <- return t
			guard (Map.keys fs == Map.keys ts) (fieldMismatch fs ts)
			mcs <- Trav.sequence (Map.mapWithKey (\k f -> fold f (Just (ts ! k))) fs)
			return (Record (fmap fst mcs), t)
		
		expr (Inject k e) Nothing = lift (Left "Cannot tag")
		expr (Inject k e) (Just t) = do
			In (Sum ts) <- return t
			guard (Map.member k ts) (tagMismatch k ts)
			(ce, ct) <- fold e (Just (ts ! k))
			return (Inject k ce, t)
			
		expr (Roll e) Nothing = lift (Left "Cannot roll")
		expr (Roll e) (Just t) = do
			In (Fix te) <- return t
			(ce, ct) <- fold e (Just (beta (In (Fix te)) te))
			return (Roll ce, t)
		
		expr (Apply f x) Nothing = do
			(cf, In (Func a b)) <- fold f Nothing
			(cx, ct) <- fold x (Just a)
			return (Apply cf cx, b)
		expr (Apply f x) (Just t) = do
			(cx, ct) <- fold x Nothing
			(cf, In (Func _ _)) <- fold f (Just (In (Func ct t)))
			return (Apply cf cx, t)

		expr (TApply f (PType t)) Nothing = do
			(cf, In (Forall te)) <- fold f Nothing
			return (TApply cf (PType t), beta t te)
		expr (TApply f (PType t)) (Just exp) = do
			(cf, In (Forall te)) <- fold f Nothing
			guard (exp == beta t te) (mismatch exp (beta t te))
			return (TApply cf (PType t), exp)

		expr (Project e k) Nothing = do
			(ce, In (Product ts)) <- fold e Nothing
			guard (Map.member k ts) (fieldAccess k ts)
			return (Project ce k, ts ! k)
		expr (Project e k) (Just t) = do
			(ce, In (Product ts)) <- fold e Nothing
			guard (Map.member k ts) (fieldAccess k ts)
			guard (ts ! k == t) (mismatch (ts ! k) t)
			return (Project ce k, t)
		
		expr (Case e cs) Nothing = do
			(ce, In (Sum ts)) <- fold e Nothing
			guard (Map.keys ts == Map.keys cs) (notExhaust ts cs)
			cets <- Trav.sequence (Map.mapWithKey (\k c -> cont c (ts ! k) Nothing) cs)
			let (ces, cts) = (fmap fst cets, fmap snd cets)
			let (t:ts) = Map.elems cts
			guard (all (== t) ts) (caseReturnMismatch cts)
			return (Case ce ces, t)
		expr (Case e cs) (Just t) = do
			(ce, In (Sum ts)) <- fold e Nothing
			guard (Map.keys ts == Map.keys cs) (notExhaust ts cs)
			cets <- Trav.sequence (Map.mapWithKey (\k c -> cont c (ts ! k) (Just t)) cs)
			let ces = fmap fst cets
			return (Case ce ces, t)

		expr (Unpack a b@(PBind x mt) p e) exp = do
			(cp, In (Exists te)) <- fold p Nothing
			pack <- lift (compatible mt (Just te))
			let lam = In (Annot (Lambda (PBind x pack) e) Nothing)
			let tlam = In (Annot (TLambda a lam) Nothing)
			(clam, lamtr) <- fold tlam Nothing
			let In (Annot (TLambda _ (In (Annot (Lambda _ ce) _))) _) = clam
			let In (Forall (In (Func at rt))) = lamtr
			guard (at == te) (mismatch at te)
			guard (noEscape rt) (existEscapes rt)
			let res = shift (-1) rt
			when exp (\exp -> guard (exp == res) (mismatch exp res))
			let PBind x _ = b
			return (Unpack a (Decl x) cp ce, res)

		expr (Unroll e) Nothing = do
			(ce, In (Fix te)) <- fold e Nothing
			return (Unroll ce, beta (In (Fix te)) te)
		expr (Unroll e) (Just t) = do
			(ce, In (Fix te)) <- fold e Nothing
			guard (t == beta (In (Fix te)) te) (mismatch t (beta (In (Fix te)) te))
			return (Unroll ce, t)
			
		expr e mt = lift (Left ("Type error: " ++ show e ++ " under assumption " ++ show mt))
		
		cont (PBind x mt, e) t mr = do
			guard (match t mt) (mismatch t (fromJust mt))
			(ce, ct) <- local (Map.insert x t) (fold e mr)
			return ((Decl x, ce), ct)
	
		guard True err = return ()
		guard False err = lift (Left err)

		when Nothing f = return ()
		when (Just x) f = f x

		kindOf (In t) = texp t
		texp (Product ts) = do
			ks <- Trav.sequence (fmap kindOf (Map.elems ts))
			guard (all (== In Type) ks) "Record type components must have kind Type"
			return $ In Type
		texp (Sum ts) = do
			ks <- Trav.sequence (fmap kindOf (Map.elems ts))
			guard (all (== In Type) ks) "Variant type components must have kind Type"
			return $ In Type
		texp (TIndex i) = return $ In Type
		texp (Forall t) = do
			In Type <- kindOf t
			return $ In Type
		texp (Exists t) = do
			In Type <- kindOf t
			return $ In Type
		texp (Fix t) = do
			In Type <- kindOf t
			return $ In Type
		texp (LambdaT t) = do
			k <- kindOf t
			return $ In (ArrowK (In Type) k)
		texp (ApplyT c t) = do
			In Type <- kindOf t
			In (ArrowK (In Type) k) <- kindOf c
			return k












data Free v k = Free (Set v) v

data ExpRec2 v r
	= Variable2 v
	| Recur2 v r
	| Lambda2 (Map v (Type String)) v r
	| TLambda2 v r
	| Record2 [r]
	| Pack2 (Type String) r
	| Inject2 Nat r
	| Roll2 r
	| Apply2 r r
	| TApply2 r (Type String)
	| Project2 r Nat
	| Unpack2 v v r r
	| Case2 r [(v, r)]
	| Unroll2 r
	| Constant2 (Type String) Value
	deriving (Show)

type Expr2 v a = Fix (Annot (ExpRec2 v) a)

tuple :: Expr PType Clos v String (Type String) -> Expr2 v (Type String)
tuple = fold
	where	fold (In a) = In (annot a)
		
		annot (Annot e t) = Annot (expr e t) t
			
		expr (Variable x) _ = Variable2 x
		expr (Recur (Clos f x) e) _ = Recur2 x (fold e)
		expr (Lambda (Clos f x) e) _ = Lambda2 f x (fold e)
		expr (TLambda a e) _ = TLambda2 a (fold e)
		expr (Record fs) _ = Record2 (fmap fold (Map.elems fs))
		expr (Pack (PType t) e) _ = Pack2 t (fold e)
		expr (Inject k e) (In (Sum fs)) = Inject2 i (fold e)
			where	Just i = elemIndex k (Map.keys fs)
		expr (Roll e) _ = Roll2 (fold e)
		expr (Apply f x) _ = Apply2 (fold f) (fold x)
		expr (TApply f (PType t)) _ = TApply2 (fold f) t
		expr (Project e k) _ = Project2 e' i
			where	e' = fold e
				In (Product fs) = typeof e'
				Just i = elemIndex k (Map.keys fs)
		expr (Unpack a (Clos f x) e1 e2) _ = Unpack2 a x (fold e1) (fold e2)
		expr (Case e cs) _ = Case2 (fold e) (fmap cont (Map.elems cs))
		expr (Unroll e) _ = Unroll2 (fold e)
		expr (Constant t v) _ = Constant2 t v
		
		cont (Clos _ x, e) = (x, fold e)

		typeof (In (Annot _ t)) = t


data Clos v k = Clos (Map v (Type k)) v

closurePack ts e = runReader (fold e) ts
	where	fold (In a) = In <$> annot a
	
		annot (Annot e t) = Annot <$> expr e t <*> pure t
		
		expr (Variable x) _ = return (Variable x)
		expr (Recur (Free f x) e) t = do
			ts <- typesof f
			Recur (Clos ts x) <$> local (addType x t) (fold e)
		expr (Lambda (Free f x) e) (In (Func t _)) = do
			ts <- typesof f
			Lambda (Clos ts x) <$> local (addType x t) (fold e)
		expr (TLambda a e) _ = TLambda a <$> fold e
		expr (Record fs) _ = Record <$> Trav.sequence (fmap fold fs)
		expr (Pack t e) _ = Pack t <$> fold e
		expr (Inject k e) _ = Inject k <$> fold e
		expr (Roll e) _ = Roll <$> fold e
		expr (Apply f x) _ = Apply <$> fold f <*> fold x
		expr (TApply f t) _ = TApply <$> fold f <*> pure t
		expr (Project e k) _ = Project <$> fold e <*> pure k
		expr (Unpack a (Free f x) e1 e2) _ = do
			ts <- typesof f
			let In (Exists t) = typeof e1
			Unpack a (Clos ts x) <$> fold e1 <*> local (addType x t) (fold e2)
		expr (Case e cs) _ = Case <$> fold e <*> Trav.sequence (Map.mapWithKey (\k c -> cont c (ts ! k)) cs)
			where	In (Sum ts) = typeof e
		expr (Unroll e) _ = Unroll <$> fold e
		expr (Constant t v) _ = return (Constant t v)

		cont (Free f x, e) t = do
			ts <- typesof f
			(,) (Clos ts x) <$> local (Map.insert x t) (fold e)

		typeof (In (Annot _ t)) = t
		
		typesof f = ask >>= \env -> return (maps (env !) f)
		addType x t = Map.insert x t . fmap (shift 1)



freeVars :: (Ord v) => Expr PType Decl v k (Type k) -> Expr PType Free v k (Type k)
freeVars = fst . runWriter . fold
	where	fold (In a) = In <$> annot a
	
		annot (Annot e t) = Annot <$> expr e <*> pure t
		
		expr (Variable x) = Variable <$> occur x
		expr (Recur (Decl x) e) = do
			(e', f) <- binding x (fold e)
			return (Recur (Free f x) e')
		expr (Lambda (Decl x) e) = do
			(e', f) <- binding x (fold e)
			return (Lambda (Free f x) e')
		expr (TLambda a e) = TLambda a <$> fold e
		expr (Record fs) = Record <$> Trav.sequence (fmap fold fs)
		expr (Pack t e) = Pack t <$> fold e
		expr (Inject k e) = Inject k <$> fold e
		expr (Roll e) = Roll <$> fold e
		expr (Apply f x) = Apply <$> fold f <*> fold x
		expr (TApply f t) = TApply <$> fold f <*> pure t
		expr (Project e k) = Project <$> fold e <*> pure k
		expr (Unpack a (Decl x) e1 e2) = do
			(e2', f) <- binding x (fold e2)
			Unpack a (Free f x) <$> fold e1 <*> pure e2'
		expr (Case e cs) = Case <$> fold e <*> Trav.sequence (fmap cont cs)
		expr (Unroll e) = Unroll <$> fold e
		expr (Constant t v) = return (Constant t v)
		
		cont (Decl x, e) = do
			(e', f) <- binding x (fold e)
			return (Free f x, e')
		
		occur x = tell (Set.singleton x) >> return x
		binding x = listen . censor (Set.delete x)



data ExpRec3 r
	= Index3 Nat
	| Recur3 r
	| Lambda3 (Arr.Array Int (Type String)) (Arr.Array Int Nat) r
	| TLambda3 r -- (Arr.Array Int (Type String)) (Arr.Array Int Nat) r
	| Record3 (Arr.Array Int r)
	| Pack3 (Type String) r
	| Inject3 Nat r
	| Roll3 r
	| Apply3 r r
	| TApply3 r (Type String)
	| Project3 r Nat
	| Unpack3 r r
	| Case3 r (Arr.Array Int r)
	| Unroll3 r
	| Constant3 (Type String) Value
	deriving (Show)

type Expr3 a = Fix (Annot ExpRec3 a)



debruijn env e = runReader (fold e) env
	where	fold (In a) = In <$> annot a
	
		annot (Annot e t) = Annot <$> expr e <*> pure t
		
		expr (Variable2 x) = do
			Just i <- elemIndex x <$> ask
			return (Index3 i)
		expr (Recur2 x e) = Recur3 <$> local (x:) (fold e)
		expr (Lambda2 free x e) = do
			scope <- ask
			let (env, ts) = unzip (Map.assocs free)
			let Just is = Trav.mapM (\y -> elemIndex y scope) env
			Lambda3 (Main.fromList ts) (Main.fromList is) <$> local (const (x:env)) (fold e)
		expr (TLambda2 a e) = TLambda3 <$> fold e
		expr (Record2 es) = Record3 . Main.fromList <$> Trav.mapM fold es
		expr (Pack2 t e) = Pack3 t <$> fold e
		expr (Inject2 i e) = Inject3 i <$> fold e
		expr (Roll2 e) = Roll3 <$> fold e
		expr (Apply2 f x) = Apply3 <$> fold f <*> fold x
		expr (TApply2 f t) = TApply3 <$> fold f <*> pure t
		expr (Project2 e i) = Project3 <$> fold e <*> pure i
		expr (Unpack2 a x e1 e2) = Unpack3 <$> fold e1 <*> local (x:) (fold e2)
		expr (Case2 e cs) = Case3 <$> fold e <*> (Main.fromList <$> Trav.sequence (fmap cont cs))
		expr (Unroll2 e) = Unroll3 <$> fold e
		expr (Constant2 t v) = return (Constant3 t v)
		
		cont (x, e) = local (x:) (fold e)



type Erase = Fix ExpRec3

erase :: Expr3 (Type k) -> (Type k, Erase)
erase = top
	where	top e = (typeof e, fold e)
	
		fold (In a) = In (annot a)
	
		annot (Annot e _) = expr e
		
		expr (Index3 x) = Index3 x
		expr (Recur3 e) = Recur3 (fold e)
		expr (Lambda3 t f e) = Lambda3 t f (fold e)
		expr (TLambda3 e) = TLambda3 (fold e)
		expr (Record3 es) = Record3 (fmap fold es)
		expr (Pack3 t e) = Pack3 t (fold e)
		expr (Inject3 i e) = Inject3 i (fold e)
		expr (Roll3 e) = Roll3 (fold e)
		expr (Apply3 f x) = Apply3 (fold f) (fold x)
		expr (TApply3 f t) = TApply3 (fold f) t
		expr (Project3 e i) = Project3 (fold e) i
		expr (Unpack3 e1 e2) = Unpack3 (fold e1) (fold e2)
		expr (Case3 e cs) = Case3 (fold e) (fmap fold cs)
		expr (Unroll3 e) = Unroll3 (fold e)
		expr (Constant3 t v) = Constant3 t v

		typeof (In (Annot _ t)) = t





data ValueRec k r
	= RecVal (Arr.Array Int r)
	| InjVal Nat r
	| LamVal (Arr.Array Int (Type k)) Erase (Arr.Array Int r) [Type k]
	| PackVal (Type k) r
	| TLamVal Erase (Env r) [Type k]
	| RollVal r

instance (Show k, Show r) => Show (ValueRec k r) where
	show (RecVal fs) = show fs
	show (InjVal i r) = show i ++ ":" ++ show r
	show (LamVal ts e env tsyn) = show ts ++ ", " ++ show env ++ ", " ++ show e ++ ", " ++ show tsyn
	show (TLamVal e env tsyn) = show env ++ ", " ++ show e ++ ", " ++ show tsyn
	show (PackVal t v) = show t ++ ", " ++ show v
	show (RollVal v) = "roll " ++ show v

type Value = Fix (ValueRec String)

type Dynamic k = (Type k, Value)




data Env v = Near v (Env v) | Far (Arr.Array Int v)	deriving (Show)


evaluate env e = eval e (env, [])
	where	eval (In e) env = step e env
	
		step (Index3 i) (env, _) = lookup env i
		step (Recur3 e) (env, tsyn) = let x = eval e (Near x env, tsyn) in x
		step (Constant3 _ v) env = v
		
		step (Lambda3 ts free e) (env, tsyn) = In (LamVal ts e (fmap (lookup env) free) tsyn)
		step (TLambda3 e) (env, tsyn) = In (TLamVal e env tsyn)
		step (Record3 es) env = In (RecVal (fmap (\e -> eval e env) es))
		step (Pack3 t e) (env, tsyn) = In (PackVal (evalType tsyn t) (eval e (env, tsyn)))
		step (Inject3 i e) env = In (InjVal i (eval e env))
		step (Roll3 e) env = In (RollVal (eval e env))
		
		step (Apply3 f x) env = apply (eval f env) (eval x env)
		step (TApply3 f t) (env, tsyn) = tapply (eval f (env, tsyn)) (evalType tsyn t)
		step (Project3 e i) env = project (eval e env) i
		step (Unpack3 e1 e2) env = unpack (eval e1 env) (e2, env)
		step (Case3 e cs) env = caseof (eval e env) (cs, env)
		step (Unroll3 e) env = unroll (eval e env)
		
		apply (In (LamVal ts e env tsyn)) v = eval e (Near v (Far env), tsyn)
		tapply (In (TLamVal e env tsyn)) t = eval e (env, t:tsyn)
		project (In (RecVal vs)) i = index vs i
		unpack (In (PackVal t v)) (e, (env, tsyn)) = eval e (Near v env, t:tsyn)
		caseof (In (InjVal i v)) (cs, (env, tsyn)) = eval (index cs i) (Near v env, tsyn)
		unroll (In (RollVal v)) = v

		lookup (Near v _) 0 = v
		lookup (Near _ r) (i+1) = lookup r i
		lookup (Far env) i = index env i
		
		
evalType env t = eval t (env, 0)
	where	eval (In t) env = In (step t env)
	
		step (TIndex i) (env, n) = if (i < n) then (TIndex i) else (out $ env !! i)
		step (Product ts) env = Product (fmap (\t -> eval t env) ts)
		step (Sum ts) env = Sum (fmap (\t -> eval t env) ts)
		step (Func a b) env = Func (eval a env) (eval b env)
		step (Exists t) (env, n) = Exists (eval t (env, n+1))
		step (Forall t) (env, n) = Forall (eval t (env, n+1))
		step (Fix t) (env, n) = Fix (eval t (env, n+1))





data Command v k = Let v (Type k, Erase)
		 | NewType v (Kind, Type k)
		 | Eval (Type k, Erase)
		 | TypeEval (Kind, Type k)
		 | Typeof (Type k, Erase)
		 | LetUnpack v v (Type k, Erase)
		 | LetUntag v (Type k, Erase)
		 | ReturnVal (Type k, Erase)
		 | Self
		 | Dump
		 | Quit







parseComm (ts, tsyn) s = maybe (Left "Parse Error") id (evalParser tokens s >>= process)
	where	process toks	 = evalParser ptype toks
				<|> evalParser pdump toks
				<|> evalParser pnewt toks
				<|> evalParser pquit toks
				<|> evalParser petype toks
				<|> evalParser punpack toks
				<|> evalParser pself toks
				<|> evalParser puntag toks
				<|> evalParser preturn toks
				<|> evalParser plet toks
				<|> (fmap Eval <$> evalParser pexp toks)

		command name post = do
			single LexColon
			x <- variableTok
			guard (name == x)
			post

		punpack = do
			single LexUnpack
			single LexOpenCurly
			a <- variableTok
			single LexComma
			x <- variableTok
			single LexCloseCurly
			single LexFrom
			e <- pexp
			return (LetUnpack a x <$> e)
			
		puntag = do
			single LexUntag
			x <- variableTok
			single LexFrom
			e <- pexp
			return (LetUntag x <$> e)

		pnewt = do
			single LexType
			a <- variableTok
			as <- many variableTok
			single LexEqual
			vt <- abstractType <$> parseType <* end
			let w = runReader (wellScopedType vt) (domain tsyn)
			if not w
				then return (Left "Scope error")
				else do 
					let t = runReader (bruijnTVars tsyn vt) []
					return (return (NewType a (In Type, t)))
		
		petype = command "k" $ do
			vt <- abstractType <$> parseType <* end
			let t = runReader (bruijnTVars tsyn vt) []
			let w = runReader (wellScopedType vt) (domain tsyn)
			return $ if not w
				then (Left "Scope error")
				else (return (TypeEval (In Type, t)))
		
		preturn = command "r" $ do
			e <- pexp
			return (ReturnVal <$> e)
			
		pquit = command "q" $ do
			return (return Quit)
		
		pdump = command "d" $ do
			return (return Dump)
		
		pself = command "self" $ do
			return (return Self)
		
		ptype = command "t" $ do
			e <- pexp
			return (Typeof <$> e)
			
		plet = do
			single LexLet
			x <- variableTok
			single LexEqual
			e <- pexp
			return (Let x <$> e)
		pexp = do
			pe <- parseTerm
			let e = abstract pe
			let w = wellScoped (domain ts, domain tsyn) e
			return $ if not w
				then Left "Scope error"
				else typecheck ts (bruijnTypes tsyn e) >>= return . erase . debruijn (Map.keys ts) . tuple . closurePack ts . freeVars


repl = loop (Map.empty, Map.empty)
	where	loop (env, tsyn) = do
			s <- prompt "> "
			let p = parseComm (types env, tsyn) s
			case p of
				Left e -> print e >> loop (env, tsyn)
				Right c -> case c of
					Let x (t, e) -> do
						let v = evaluate (values env) e
						printExp x (t, v)
						loop (Map.insert x (t, v) env, tsyn)
					Eval (t, e) -> do
						let v = evaluate (values env) e
						printExp "it" (t, v)
						loop (env, tsyn)
					NewType a (k, t) -> do
						printType a t
						loop (env, Map.insert a t tsyn)
					TypeEval (k, t) -> do
						printType "it" t
						loop (env, tsyn)
					LetUnpack a x (In (Exists te), e) -> do
						let In (PackVal t v) = evaluate (values env) e
						let hidden = beta t te
						printType a t
						printExp x (hidden, v)
						loop (Map.insert x (hidden, v) env, Map.insert a t tsyn)
					LetUnpack a x _ -> print "Type error in Unpack" >> loop (env, tsyn)
					LetUntag x (In (Sum ts), e) -> do
						let In (InjVal tag v) = evaluate (values env) e
						let (l, t) = Map.assocs ts !! tag
						putStr "Label = "
						print l
						printExp x (t, v)
						loop (Map.insert x (t, v) env, tsyn)
					LetUntag x _ -> print "Type error in Untag" >> loop (env, tsyn)
					Typeof (t, _) -> do
						printType "it" t
						loop (env, tsyn)
					Dump -> do
						Trav.forM (Map.assocs env) (uncurry printExp)
						putStrLn ""
						Trav.forM (Map.assocs tsyn) (uncurry printType)
						loop (env, tsyn)
					Self -> do
						print typeType
						loop (env, tsyn)
					ReturnVal (t, e) -> do
						let v = evaluate (values env) e
						return (In (PackVal t v))
					Quit -> print "Session terminated." >> return nil

		types = fmap fst
		values = Far . Main.fromList . fmap snd . Map.elems
		
		printExp x (t, v) = do
			putStr (x ++ " : ")
			print t
			putStr (x ++ " = ")
			print v
		
		printType x t = do
			putStrLn (x ++ " : *")
			putStr (x ++ " = ")
			print t

		nil = In $ PackVal (In $ Product Map.empty) (In $ RecVal (Main.fromList []))
