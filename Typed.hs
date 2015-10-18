import Parser
import Control.Applicative as App
import Data.Map as Map
import Data.Traversable as Trav
import Data.Set as Set
import Data.List as List
import Control.Monad.Reader as Read
import Control.Monad.Writer as Write hiding (Sum, Product, pass)
import Control.Monad.State
import Control.Monad.Error
import Debug.Trace
import Data.Either
import qualified Data.Foldable




{--

kind = <
  Type
  Arrow : kind * kind
>

type ((n, ks):array kind) (k:kind) = <
  Index : enum n
  Intro : case k of
    Type -> <
      Func : type (n, ks) Type * type (n, ks) Type
      Product : (m:nat) * vector m (type (n, ks) Type)
      Sum : (m:nat) * vector m (type (n, ks) Type)
      Forall : (h:kind) * type (1+n, (h, ks)) Type
      Exists : (h:kind) * type (1+n, (h, ks)) Type
      Fix : type (1+n, (Type, ks)) Type
    >
    Arrow a b -> type (1+n, (a, ks)) b
  Apply : (h:kind) * type n ks (Arrow h k) * type n ks h
>

expr ((m, ks):array kind) ((n, ts):array (type (m, ks) Type)) (t:type (m, ks) Type) = <
  Index : enum n
  Intro : case t of
    Intro (Func a b) -> expr (m, ks) (1+n, (a, ts)) b
    Intro (Forall k c) -> expr (1+m, (k, ks)) (fmap (shift 1) (n, ts)) c
    Intro (Product m cs) -> zip m (expr (m, ks) (n, ts)) cs
    Intro (Sum m cs) -> (i:enum m) * expr (m, ks) (n, ts) cs[i]
    Intro (Fix c) -> expr (m, ks) (n, ts) (beta (Fix c) c)
    _ -> ((a:*) -> a)
  Apply : (a:type (m, ks) Type) * expr (m, ks) (n, ts) (Intro (Func a t))
  ApplyT : (k:kind) * (c:type (1+m, (k, ks)) Type) * (a:type (m, ks) Type) * expr (m, ks) (n, ts) (Intro (Forall k c)) * (beta a c = t)
  Project : (p:nat) * (cs:vector p (type (m, ks) Type)) * (i:enum (1+p)) * expr (m, ks) (n, ts) (insertAt p i t cs)
  Case : (p:nat) * (cs:vector p (type (m, ks) Type)) * zip (\i:enum p -> expr (m, ks) (n, ts) cs[i]) (enumTo p)
  Unroll : (c:type (1+m, (Type, ks)) Type) * expr (m, ks) (n, ts) (Intro (Fix c))
>

--}





fromJust (Just x) = x

type Nat = Int

data Fix f
	= In { out :: f (Fix f) }

instance (Show (f (Fix f))) => Show (Fix f) where
	show (In x) = "(" ++ show x ++ ")" 

instance (Eq (f (Fix f))) => Eq (Fix f) where
	In x == In y = x == y

{--
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

instance Applicative (State s) where
	pure = return
	(<*>) = ap

--}

fresh = do
	x <- get
	put (x+1)
	return x

  	
  	


  	
  	




toExc err Nothing = throwError err
toExc err (Just v) = return v

compile str = do
	e <- toExc "Parse error" (parse str)
	check (checkScope e emptyScope) "Scope error"
	let e' = bruijn e emptyOrdScope
	(ct, ce) <- typecheck e' Nothing emptyTypeEnv
	let (zt, ze) = reduceTrivial (struct (ct, ce))
	() <- runReaderT (lint (zt, ze)) emptyLintEnv
	return (zt, ze)
--	let (s, v) = valueOf (zt, ze) emptyEvalEnv
--	return (s, v)



main = do
	str <- readFile "program.fo"
	print (compile str)







data Token v k
	= LexVariable v
	| LexKeyword k
	| LexOpenParen
	| LexCloseParen
	| LexOpenSquare
	| LexCloseSquare
	| LexOpenCurly
	| LexCloseCurly
	| LexComma
	| LexColon
	| LexLambda
	| LexTLambda
	| LexForall
	| LexRoll
	| LexUnroll
	| LexFix
	| LexCase
	| LexOf
	| LexArrow
	| LexBar
	| LexEqual
	| LexSemicolon
	| LexType
	| LexLet
	| LexIn
	| LexStar
	| LexDot
	deriving (Show, Eq)

tokens :: Parser [Token String String]
tokens = lexical token whiteSpace
	where	token	 =  onStr "->" LexArrow
			<|> onStr "/\\" LexTLambda
			<|> onStr "\\/" LexForall
			<|> onChr ':' LexColon
			<|> onChr '.' LexDot
			<|> onChr '*' LexStar
			<|> onChr ',' LexComma
			<|> onChr '\\' LexLambda
			<|> onChr '(' LexOpenParen
			<|> onChr ')' LexCloseParen
			<|> onChr '[' LexOpenSquare
			<|> onChr ']' LexCloseSquare
			<|> onChr '{' LexOpenCurly
			<|> onChr '}' LexCloseCurly
			<|> onChr '|' LexBar
			<|> onChr '=' LexEqual
			<|> onChr ';' LexSemicolon
			<|> (LexKeyword <$> keyword)
			<|> (unamb <$> identifier)
			
		unamb "forall" = LexForall
		unamb "lambda" = LexLambda
		unamb "case" = LexCase
		unamb "of" = LexOf
		unamb "type" = LexType
		unamb "let" = LexLet
		unamb "in" = LexIn
		unamb "fix" = LexFix
		unamb "roll" = LexRoll
		unamb "unroll" = LexUnroll
		unamb x = LexVariable x

		identifier = (:) <$> lower <*> many letter
		keyword = (:) <$> upper <*> many letter
		
		space = many ((space >> return "") <|> comment)
		comment = allOf "//" >> many (sat (/= '\n'))


variableTok = do
	t <- item
	case t of 
		LexVariable x -> return x
		_ -> abort

keywordTok = do
	t <- item
	case t of
		LexKeyword k -> return k
		_ -> abort






















	
type Ident = String
type Keyword = String

data PValue t k
	= PVariable Ident
	| PLoneTag Keyword
	| PLambda Ident (Maybe (t k)) (PAnnot t k)
	| PLambdaT Ident (Maybe k) (PAnnot t k)
	| PRecord (Map Keyword (PAnnot t k))
	| PCase (PAnnot t k) (Map Keyword (PCont t k))
	| PLet [PStatement t k] (PAnnot t k)
	| PRecur Ident (Maybe (t k)) (PAnnot t k)
	| PParen (PAnnot t k)
	deriving (Show)

data PStatement t k
	= PDefValue Bool Ident (Maybe (t k)) (PAnnot t k)
	| PDefType Ident (Maybe k) (t k)
	deriving (Show)

data PCont t k
	= PCont (Maybe (Ident, Maybe (t k))) (PAnnot t k)
	deriving (Show)
	
data PProj t k
	= PProj (PValue t k) [Keyword]
	deriving (Show)

data PHead t k
	= PInject Keyword (PProj t k)
	| PRoll (PProj t k)
	| PUnroll (PProj t k)
	| PFunHead (PProj t k)
	deriving (Show)
	
data PExpr t k
	= PApply (PHead t k) [Either (PProj t k) (t k)]
	deriving (Show)

data PAnnot t k
	= PAnnot (PExpr t k) (Maybe (t k))
	deriving (Show)

data PTValue k
	= PTParen (PTAnnot k)
	| PTVariable Ident
	| PTLambda Ident (Maybe k) (PTAnnot k)
	| PTForall Ident (Maybe k) (PTAnnot k)
	| PTProduct (Map Keyword (PTAnnot k))
	| PTFix Ident (PTAnnot k)
	deriving (Show)

data PTApp k
	= PTApp (PTValue k) [PTValue k]
	deriving (Show)

data PTExpr k
	= PFunc [PTApp k] (PTApp k)
	| PTSum (Map Keyword (Maybe (PTValue k)))
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
			mt <- typeAnnot
			return (PAnnot e mt)
			
		typeAnnot = annot (prsT prsK)
		
		expression = apply
		apply = PApply <$> head <*> many (proj <||> targ)
		
		head = inject <|> roll <|> unroll <|> (PFunHead <$> proj)
		
		inject = PInject <$> keywordTok <*> proj
		roll = single LexRoll >> PRoll <$> proj
		unroll = single LexUnroll >> PUnroll <$> proj

		targ = do
			single LexOpenSquare
			t <- prsT prsK
			single LexCloseSquare
			return t

		proj	 = do
			v <- value
			ks <- many (single LexDot >> keywordTok)
			return (PProj v ks)
			
		value	 =  variable
			<|> lonetag
			<|> lambda
			<|> lambdaT
			<|> record
			<|> caseof
			<|> letdefs
			<|> recur
			<|> (PParen <$> inparen annotation)
		
		variable = PVariable <$> variableTok

		lonetag = PLoneTag <$> keywordTok
		
		lambda = do
			single LexLambda
			x <- variableTok
			mt <- typeAnnot
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
	
		record = PRecord <$> recordOf annotation
		
		caseof = do
			single LexCase
			e <- annotation
			single LexOf
			single LexOpenCurly
			ks <- sepBy LexSemicolon cont <|> return []
			single LexCloseCurly
			return (PCase e (Map.fromList ks))
			
		cont = do
			k <- keywordTok
			bind <- optional ((,) <$> variableTok <*> typeAnnot)
			single LexDot
			e <- annotation
			return (k, (PCont bind e))

		letdefs = do
			single LexLet
			defs <- sepBy LexSemicolon (defType <|> defVal)
			single LexIn
			e <- annotation
			return (PLet defs e)
		
		defType = do
			single LexType
			x <- variableTok
			mk <- annot prsK
			single LexEqual
			t <- prsT prsK
			return (PDefType x mk t)
		
		defVal = do
			rec <- maybe False (const True) <$> optional (single LexFix)
			x <- variableTok
			mt <- typeAnnot
			single LexEqual
			e <- annotation
			return (PDefValue rec x mt e)
		
		recur = do
			single LexFix
			x <- variableTok
			mt <- typeAnnot
			single LexDot
			e <- annotation
			return (PRecur x mt e)
			
			

parseType prsK = annotation
	where	annotation = do
			e <- expression
			mt <- annot prsK
			return (PTAnnot e mt)

		expression = sum <|> func
		
		sum = do
			ts <- Map.fromList <$> sepBy LexBar tagged
			return (PTSum ts)
		
		tagged = (,) <$> keywordTok <*> optional value
		
		func = PFunc <$> many (application <* single LexArrow) <*> application
		
		application = PTApp <$> value <*> many value

		value	 = variable
			<|> lambda
			<|> forall
			<|> product
			<|> fixpoint
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
		
		product = PTProduct <$> recordOf annotation
		
		fixpoint = do
			single LexFix
			x <- variableTok
			_ <- optional (single LexColon >> single LexStar)
			single LexDot
			e <- annotation
			return (PTFix x e)

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

recordOf p = do
	single LexOpenCurly
	fs <- sepBy LexComma (fieldOf p) <|> return []
	single LexCloseCurly
	return (Map.fromList fs)

fieldOf p = do
	k <- keywordTok
	single LexColon
	x <- p
	return (k, x)























data Expr bind v
	= Variable v
	| Recur (bind v (Type bind v)) (Expr bind v)
	| Lambda (bind v (Type bind v)) (Expr bind v)
	| LambdaT (bind v Kind) (Expr bind v)
	| Record (Map Keyword (Expr bind v))
	| Inject Keyword (Expr bind v)
	| Roll (Expr bind v)
	| DefType (bind v Kind) (Type bind v) (Expr bind v)
	| Apply (Expr bind v) (Expr bind v)
	| ApplyT (Expr bind v) (Type bind v)
	| Project (Expr bind v) Keyword
	| Case (Expr bind v) (Map Keyword (bind v (Type bind v), Expr bind v))
	| Unroll (Expr bind v)
	| TypeAnnot (Expr bind v) (Type bind v)
deriving instance (Eq (bind v (Type bind v)), Eq (bind v Kind), Eq (Type bind v), Eq v) => Eq (Expr bind v)
deriving instance (Show (bind v (Type bind v)), Show (bind v Kind), Show (Type bind v), Show v) => Show (Expr bind v)
	
data Type bind v
	= Func (Type bind v) (Type bind v)
	| Forall (bind v Kind) (Type bind v)
	| Product (Map Keyword (Type bind v))
	| Sum (Map Keyword (Type bind v))
	| Fix (bind v ()) (Type bind v)
	| TVariable v
	| TLambda (bind v Kind) (Type bind v)
	| TApply (Type bind v) (Type bind v)
	| KindAnnot (Type bind v) Kind
deriving instance (Eq (bind v Kind), Eq (bind v ()), Eq (Expr bind v), Eq v) => Eq (Type bind v)
deriving instance (Show (bind v Kind), Show (bind v ()), Show (Expr bind v), Show v) => Show (Type bind v)

data Kind
	= Type
	| Arrow Kind Kind
	deriving (Eq)

instance Show Kind where
	show Type = "*"
	show (Arrow k h) = "(" ++ show k ++ " -> " ++ show h ++ ")"

data Decl v ann
	= Decl v (Maybe ann)
	deriving (Eq, Show)

data Annot v ann
	= Annot ann
	| NoAnnot
	deriving (Eq, Show)

	


abstractTerm abst absk = annot
	where	annot (PAnnot pe Nothing) = expr pe
		annot (PAnnot pe (Just t)) = TypeAnnot (expr pe) (abst absk t)
		
		expr (PApply pf pxs) = foldl apply (head pf) (fmap abs pxs)
			where	apply f (Left v) = Apply f v
				apply f (Right t) = ApplyT f t
			
				abs (Left v) = Left (proj v)
				abs (Right t) = Right (abst absk t)

		head (PInject k px) = Inject k (proj px)
		head (PRoll pe) = Roll (proj pe)
		head (PUnroll pe) = Unroll (proj pe)
		head (PFunHead pe) = proj pe
		
		proj (PProj px ks) = foldl Project (value px) ks

		value (PVariable x) = Variable x
		value (PLoneTag k) = Inject k (Record Map.empty)
		value (PLambda x mt pe) = Lambda (Decl x (abst absk <$> mt)) (annot pe)
		value (PLambdaT x mk pe) = LambdaT (Decl x (absk <$> mk)) (annot pe)
		value (PRecord fs) = Record (fmap annot fs)
		value (PCase e ks) = Case (annot e) (cont <$> ks)
		value (PLet defs pe) = foldr undef (annot pe) defs
		value (PRecur x mt pe) = Recur (Decl x (abst absk <$> mt)) (annot pe)
		value (PParen pe) = annot pe

		undef (PDefType a mk pt) body = DefType (Decl a (absk <$> mk)) (abst absk pt) body
		undef (PDefValue rec x mt pe) body = Apply (Lambda (Decl x ann) body) arg
			where	ann = abst absk <$> mt
				exp = annot pe
				inner	| rec = Recur (Decl x Nothing) exp
					| otherwise = exp
				arg = maybe inner (TypeAnnot inner) ann
	
		cont (PCont Nothing pe) = (Decl "_" (Just (Product Map.empty)), annot pe)
		cont (PCont (Just (x, mt)) pe) = (Decl x (abst absk <$> mt), annot pe)
		
abstractType absk = annot
	where	annot (PTAnnot pe Nothing) = expr pe
		annot (PTAnnot pe (Just k)) = KindAnnot (expr pe) (absk k)
		
		expr (PTSum pvs) = Sum (maybe (Product Map.empty) value <$> pvs)
		expr (PFunc pvs pv) = foldr Func (app pv) (app <$> pvs)
		
		app (PTApp pv pvs) = foldl TApply (value pv) (value <$> pvs)

		value (PTParen pa) = annot pa
		value (PTVariable a) = TVariable a
		value (PTLambda x mk pe) = TLambda (Decl x (absk <$> mk)) (annot pe)
		value (PTForall x mk pe) = Forall (Decl x (absk <$> mk)) (annot pe)
		value (PTProduct fs) = Product (fmap annot fs)
		value (PTFix x pe) = Fix (Decl x Nothing) (annot pe)

abstractKind = expr
	where	expr (PKFunc pvs pv) = foldr Arrow (value pv) (value <$> pvs)
	
		value PKType = Type
		value (PKParen pe) = expr pe

abstract = abstractTerm abstractType abstractKind


parse = tokenize >=> structure >=> return . abstract
	where	tokenize = evalParser tokens
		structure = evalParser (parseTerm parseType parseKind)


















emptyScope = (Set.empty, Set.empty)
putTermVar x (vs, ts) = (Set.insert x vs, ts)
putTypeVar a (vs, ts) = (vs, Set.insert a ts)
termVarInScope x (vs, ts) = Set.member x vs
typeVarInScope a (vs, ts) = Set.member a ts

checkTermScope checkT = fold
	where	fold (Variable v) = termVarInScope v <$> ask
		fold (Recur (Decl x ann) e) = (&&) <$> annot ann <*> local (putTermVar x) (fold e)
		fold (Lambda (Decl x ann) e) = (&&) <$> annot ann <*> local (putTermVar x) (fold e)
		fold (LambdaT (Decl a ann) e) = local (putTypeVar a) (fold e)
		fold (Record fs) = Map.fold (&&) True <$> Trav.mapM fold fs
		fold (Inject k e) = fold e
		fold (Roll e) = fold e
		fold (DefType (Decl a ann) t e) = (&&) <$> checkT t <*> local (putTypeVar a) (fold e)
		fold (Apply f x) = (&&) <$> fold f <*> fold x
		fold (ApplyT f t) = (&&) <$> fold f <*> checkT t
		fold (Project p k) = fold p
		fold (Case e ks) = Map.fold (&&) <$> fold e <*> Trav.mapM cont ks
		fold (Unroll e) = fold e
		fold (TypeAnnot e t) = (&&) <$> fold e <*> checkT t
		cont (Decl x ann, e) = (&&) <$> annot ann <*> local (putTermVar x) (fold e)
		
		annot Nothing = return True
		annot (Just t) = checkT t
		

checkTypeScope = fold
	where	fold (Func a b) = (&&) <$> fold a <*> fold b
		fold (Forall (Decl a mk) t) = local (putTypeVar a) (fold t)
		fold (Product fs) = Map.fold (&&) True <$> Trav.mapM fold fs
		fold (Sum fs) = Map.fold (&&) True <$> Trav.mapM fold fs
		fold (Fix (Decl a _) t) = local (putTypeVar a) (fold t)
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
		fold (Recur (Decl x ann) e) = Recur <$> annot brjT ann <*> local (putTermName x) (fold e)
		fold (Lambda (Decl x ann) e) = Lambda <$> annot brjT ann <*> local (putTermName x) (fold e)
		fold (LambdaT (Decl a ann) e) = LambdaT <$> annot return ann <*> local (putTypeName a) (fold e)
		fold (Record fs) = Record <$> Trav.mapM fold fs
		fold (Inject k e) = Inject k <$> fold e
		fold (Roll e) = Roll <$> fold e
		fold (DefType (Decl a ann) t e) = DefType <$> annot return ann <*> brjT t <*> local (putTypeName a) (fold e)
		fold (Apply f x) = Apply <$> fold f <*> fold x
		fold (ApplyT f t) = ApplyT <$> fold f <*> brjT t
		fold (Project p k) = Project <$> fold p <*> return k
		fold (Case e ks) = Case <$> fold e <*> Trav.mapM cont ks
		fold (Unroll e) = Unroll <$> fold e
		fold (TypeAnnot e t) = TypeAnnot <$> fold e <*> brjT t

		cont (Decl x ann, e) = (,) <$> annot brjT ann <*> local (putTermName x) (fold e)
		
		annot brj Nothing = return NoAnnot
		annot brj (Just t) = Annot <$> brj t

bruijnType = fold
	where	fold (Func a b) = Func <$> fold a <*> fold b
		fold (Forall (Decl a mk) t) = Forall <$> annot mk <*> local (putTypeName a) (fold t)
		fold (Product fs) = Product <$> Trav.mapM fold fs
		fold (Sum fs) = Sum <$> Trav.mapM fold fs
		fold (Fix (Decl a _) t) = Fix NoAnnot <$> local (putTypeName a) (fold t)
		fold (TVariable a) = TVariable . typeVarIndex a <$> ask
		fold (TLambda (Decl a mk) t) = TLambda <$> annot mk <*> local (putTypeName a) (fold t)
		fold (TApply c t) = TApply <$> fold c <*> fold t
		fold (KindAnnot t k) = KindAnnot <$> fold t <*> return k
		
		annot Nothing = return NoAnnot
		annot (Just k) = return (Annot k)

bruijn = runReader . bruijnTerm bruijnType













data CType row
	= CFunc (CType row) (CType row)	-- type n ctx Type = Func : type n ctx Type * type n ctx Type
	| CForall Kind (CType row)	-- type n ctx Type = Forall : (k:Kind) * type n ctx (Arrow k Type)
	| CProduct (row (CType row))	-- type n ctx Type = Product : map keyword (type n ctx Type)
	| CSum (row (CType row))
	| CFix (CType row)
	| CTIndex Nat			-- type n ctx k = enum n
	| CTLambda (CType row)		-- type n ctx (Arrow k h) = type (1+n) (k, ctx) h
	| CTApply Kind (CType row) (CType row)	-- type n ctx k = (h:Kind) * type n ctx (Arrow h k) * type n ctx h
deriving instance (Show (row (CType row))) => Show (CType row)
deriving instance (Eq (row (CType row))) => Eq (CType row)


data CExpr
	= CIndex Nat			 -- expr r = nat
	| CRecur CExpr
	| CLambda CExpr	 		 -- expr (Func a b) = expr b
	| CLambdaT CExpr		 -- expr (Forall k c) = (t:type k) -> expr (apply c t)
	| CRecord (Map Keyword CExpr)	 -- expr (Product ts) = (k:key ts) :->: expr ts[k]
	| CInject Keyword CExpr
	| CRoll CExpr
	| CApply (CType (Map Keyword)) CExpr CExpr	 -- expr r = (t:type Star) * expr (Func t r) * expr t
	| CApplyT Kind (CType (Map Keyword)) CExpr (CType (Map Keyword)) -- expr r = (k:Kind) * (c:type (Arrow k Star)) * expr (Forall k c) * (t:type k) * (r = apply c t)
	| CProject (Map Keyword (CType (Map Keyword))) CExpr Keyword
	| CCase (Map Keyword (CType (Map Keyword))) CExpr (Map Keyword CExpr)
	| CUnroll (CType (Map Keyword)) CExpr
	deriving (Eq, Show)










emptyTypeEnv = ([], [], [])
putType t (ts, ks, syns) = (t:ts, ks, syns)
putKind k (ts, ks, syns) = (fmap (shift 1) ts, k:ks, fmap (shift 1 <$>) (Nothing:syns))
putSynonym k t (ts, ks, syns) = (fmap (shift 1) ts, k:ks, fmap (shift 1 <$>) (Just t:syns))
getType i (ts, ks, syns) = ts !! i
getKind i (ts, ks, syns) = ks !! i
getSynonyms (ts, ks, syns) = syns

inferType (Variable i) = do
	t <- getType i <$> ask
	return (t, CIndex i)
inferType (Recur NoAnnot e) = mzero
inferType (Recur (Annot t) e) = do
	a <- verifyType t Type
	ce <- local (putType a) (checkType e a)
	return (a, CRecur ce)
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
inferType (Record fs) = do
	fs <- Trav.mapM inferType fs
	return (CProduct (fmap fst fs), CRecord (fmap snd fs)) 
inferType (Inject k e) = mzero
inferType (Roll e) = mzero
inferType (DefType NoAnnot t e) = do
	(k, _) <- inferKind t
	inferType (DefType (Annot k) t e)
inferType (DefType (Annot k) t e) = do
	ct <- verifyType t k
	(r, ce) <- local (putSynonym k ct) (inferType e)
	return (shift (-1) r, CApplyT k r (CLambdaT ce) ct)
inferType (Apply f x) = do
	(CFunc a b, cf) <- inferType f
	cx <- checkType x a
	return (b, CApply a cf cx)
inferType (ApplyT f t) = do
	(CForall k e, cf) <- inferType f
	ct <- verifyType t k
	return (beta ct e, CApplyT k e cf ct)
inferType (Project p k) = do
	(CProduct ts, cp) <- inferType p
	guard (Map.member k ts)
	return (ts ! k, CProject ts cp k)
inferType (Case e ks) = do
	(CSum ts, ce) <- inferType e
	guard (Map.keys ts == Map.keys ks)
	cks <- Trav.sequence (Map.mapWithKey (\key k -> inferCont k (ts ! key)) ks)
	let q:qs = Map.elems (fmap fst cks)
	    cs = fmap snd cks
	guard (all (== q) qs)
	return (q, CCase ts ce cs)
inferType (Unroll e) = do
	(CFix t, ce) <- inferType e
	return (beta (CFix t) t, CUnroll t ce)
inferType (TypeAnnot e t) = do
	ct <- verifyType t Type
	ce <- checkType e ct
	return (ct, ce)
inferCont (NoAnnot, e) a = local (putType a) (inferType e)
inferCont (Annot t, e) a = do
	ct <- verifyType t Type
	guard (ct == a)
	local (putType a) (inferType e)

checkType (Variable i) t = do
	s <- getType i <$> ask
	guard (t == s)
	return (CIndex i)
checkType (Recur NoAnnot e) t = do
	ce <- local (putType t) (checkType e t)
	return (CRecur ce)
checkType (Recur (Annot a) e) t = do
	s <- verifyType a Type
	guard (s == t)
	ce <- local (putType t) (checkType e t)
	return (CRecur ce)
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
checkType (Record fs) (CProduct ts) = do
	guard (Map.keys fs == Map.keys ts)
	let check k e = checkType e (ts ! k)
	ces <- Trav.sequence (Map.mapWithKey check fs)
	return (CRecord ces)
checkType (Record fs) t = mzero
checkType (Inject k e) (CSum ts) = do
	guard (Map.member k ts)
	ce <- checkType e (ts ! k)
	return (CInject k ce)
checkType (Inject k e) t = mzero
checkType (Roll e) (CFix t) = do
	ce <- checkType e (beta (CFix t) t)
	return (CRoll ce)
checkType (Roll e) t = mzero
checkType (DefType NoAnnot t e) r = do
	(k, _) <- inferKind t
	checkType (DefType (Annot k) t e) r
checkType (DefType (Annot k) t e) r = do
	ct <- verifyType t k
	let cr = shift 1 r
	ce <- local (putSynonym k ct) (checkType e cr)
	return (CApplyT k cr (CLambdaT ce) ct)
checkType (Apply f x) b = do
	(a, cx) <- inferType x
	cf <- checkType f (CFunc a b)
	return (CApply a cf cx)
checkType (ApplyT f t) b = do
	(CForall k e, cf) <- inferType f
	ct <- verifyType t k
	guard (beta ct e == b)
	return (CApplyT k e cf ct)
checkType (Project p k) r = do
	(CProduct ts, cp) <- inferType p
	guard (Map.member k ts)
	guard (ts ! k == r)
	return (CProject ts cp k)
checkType (Case e ks) r = do
	(CSum ts, ce) <- inferType e
	guard (Map.keys ts == Map.keys ks)
	cks <- Trav.sequence (Map.mapWithKey (\key k -> checkCont k (ts ! key) r) ks)
	return (CCase ts ce cks)
checkType (Unroll e) r = do
	(CFix t, ce) <- inferType e
	guard (beta (CFix t) t == r)
	return (CUnroll t ce)
checkType (TypeAnnot e t) s = do
	ct <- verifyType t Type
	guard (ct == s)
	checkType e s

checkCont (NoAnnot, e) a r = local (putType a) (checkType e r)
checkCont (Annot t, e) a r = do
	ct <- verifyType t Type
	guard (ct == a)
	local (putType a) (checkType e r)

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
inferKind (Product ts) = do
	cts <- Trav.mapM (\t -> checkKind t Type) ts
	return (Type, CProduct cts)
inferKind (Sum ts) = do
	cts <- Trav.mapM (\t -> checkKind t Type) ts
	return (Type, CSum cts)
inferKind (Fix _ t) = do
	ct <- local (putKind Type) (checkKind t Type)
	return (Type, CFix ct)
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
checkKind (Product ts) Type = do
	cts <- Trav.mapM (\t -> checkKind t Type) ts
	return (CProduct cts)
checkKind (Product ts) k = mzero
checkKind (Sum ts) Type = do
	cts <- Trav.mapM (\t -> checkKind t Type) ts
	return (CSum cts)
checkKind (Sum ts) k = mzero
checkKind (Fix _ t) Type = do
	ct <- local (putKind Type) (checkKind t Type)
	return (CFix ct)
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
	ks <- getSynonyms <$> ask
	return (normalize (inlineSynonyms ks s))

typecheck e Nothing = runReaderT (inferType e)
typecheck e (Just t) = runReaderT (inferType (TypeAnnot e t))















foldType func forall product sum fix index lambda apply = rec
	where	rec (CFunc a b) = func (rec a) (rec b)
		rec (CForall k t) = forall k (rec t)
		rec (CProduct ts) = product (rec <$> ts)
		rec (CSum ts) = sum (rec <$> ts)
		rec (CFix t) = fix (rec t)
		rec (CTIndex i) = index i
		rec (CTLambda t) = lambda (rec t)
		rec (CTApply k f t) = apply k (rec f) (rec t)

foldDepth func forall product sum fix index lambda apply t = runReader (delegate t) 0
	where	delegate = foldType
			(\ra rb -> func <$> ra <*> rb)
			(\k rt -> forall k <$> local (+1) rt)
			(\rts -> product <$> Trav.sequence rts)
			(\rts -> sum <$> Trav.sequence rts)
			(\rt -> fix <$> local (+1) rt)
			(\i -> index i <$> ask)
			(\rt -> lambda <$> local (+1) rt)
			(\k rf rt -> apply k <$> rf <*> rt)

foldIndex index = foldDepth CFunc CForall CProduct CSum CFix index CTLambda CTApply

normalize = foldType CFunc CForall CProduct CSum CFix CTIndex CTLambda apply

inlineSynonyms ks = foldIndex index 
	where	index i depth
			| i < depth = CTIndex i
			| otherwise = maybe (CTIndex i) (shift depth) (ks !! (i - depth))

beta x = foldDepth CFunc CForall CProduct CSum CFix index CTLambda apply
	where	index i depth
			| i <  depth = CTIndex i
			| i == depth = shift depth x
			| i  > depth = CTIndex (i-1)
		
shift amount = foldIndex index 
	where	index i depth
			| i < depth = CTIndex i
			| otherwise = CTIndex (i + amount)

occurs = foldDepth (||) (const id) (Map.fold (||) False) (Map.fold (||) False) id (==) id (const (||))

apply k (CTLambda t) x = beta x t
apply k c x = CTApply k c x








instance Show ZExpr where
	show e = runReader (line (rec e)) ""
		where	rec (ZIndex i) = indent (return ('V':show i))
			rec (ZRecur e) = tag "Recur" (node e)
			rec (ZLambda e) = tag "Lambda" (node e)
			rec (ZLambdaT e) = tag "LambdaT" (node e)
			rec (ZTuple es) = tag "Tuple" (nodes es)
			rec (ZInject i e) = tag "Inject" (subs [basic i, rec e])
			rec (ZRoll e) = tag "Roll" (node e)
			rec (ZApply t f x) = tag "Apply" (subs [basic t, rec x, rec f])
			rec (ZApplyT k c f t) = tag "ApplyT" (subs [basic (CForall k c), basic t, rec f]) 
			rec (ZProject ts e i) = tag "Project" (subs [basic ts, basic i, rec e])
			rec (ZCase ts e ks) = tag "Case" (subs [basic ts, rec e, nodes ks])
			rec (ZUnroll t e) = tag "Unroll" (subs [basic (CFix t), rec e])
	
			indent t = (++) <$> ask <*> t
			line t = ('\n':) <$> t
			level = local (' ':)
			node t = line (rec t)
			nodes ts = concat <$> Trav.sequence (node <$> ts)
			subs ns = concat <$> Trav.sequence (line <$> ns)
			basic x = indent (return (show x))
			tag t ns = indent ((t ++) <$> level ns)

type Zipper a = ([a], [a])

data ZExpr
	= ZIndex Nat
	| ZRecur ZExpr
	| ZLambda ZExpr
	| ZLambdaT ZExpr
	| ZTuple [ZExpr]
	| ZInject Nat ZExpr
	| ZRoll ZExpr
	| ZApply (CType []) ZExpr ZExpr
	| ZApplyT Kind (CType []) ZExpr (CType []) 
	| ZProject [CType []] ZExpr Nat
	| ZCase [CType []] ZExpr [ZExpr]
	| ZUnroll (CType []) ZExpr
	deriving (Eq)







tuplesT = foldType CFunc CForall (CProduct . Map.elems) (CSum . Map.elems) CFix CTIndex CTLambda CTApply

tuples t (CIndex i) = ZIndex i
tuples t (CRecur e) = ZRecur (tuples t e)
tuples (CFunc a b) (CLambda e) = ZLambda (tuples b e)
tuples (CForall k t) (CLambdaT e) = ZLambdaT (tuples t e)
tuples (CProduct ts) (CRecord fs) = ZTuple (zipWith tuples (Map.elems ts) (Map.elems fs))
tuples (CSum ts) (CInject k e) = ZInject i (tuples (Map.elems ts !! i) e)
	where	Just i = elemIndex k (Map.keys ts)
tuples (CFix t) (CRoll e) = ZRoll (tuples (beta (CFix t) t) e)
tuples t (CApply a f x) = ZApply (tuplesT a) (tuples (CFunc a t) f) (tuples a x)
tuples t (CApplyT k c f s) = ZApplyT k (tuplesT c) (tuples (CForall k c) f) (tuplesT s)
tuples t (CProject fs p k) = ZProject (tuplesT <$> Map.elems fs) (tuples (CProduct fs) p) i
	where	Just i = elemIndex k (Map.keys fs)
tuples t (CCase ts e cs) = ZCase (tuplesT <$> Map.elems ts) (tuples (CSum ts) e) (tuples t <$> Map.elems cs)
tuples t (CUnroll r e) = ZUnroll (tuplesT r) (tuples (CFix r) e)

struct (t, e) = (tuplesT t, tuples t e)





trivialT = foldType CFunc CForall (single CProduct) (single CSum) CFix CTIndex CTLambda CTApply
	where	single tag [t] = t
		single tag ts = tag ts
		
trivial t (ZIndex i) = ZIndex i
trivial t (ZRecur e) = ZRecur (trivial t e)
trivial (CFunc a b) (ZLambda e) = ZLambda (trivial b e)
trivial (CForall k t) (ZLambdaT e) = ZLambdaT (trivial t e)
trivial (CProduct []) e = ZTuple []
trivial (CProduct [t]) (ZTuple [e]) = trivial t e
trivial (CProduct ts) (ZTuple es) = ZTuple (zipWith trivial ts es)
trivial (CSum [t]) (ZInject 0 e) = trivial t e
trivial (CSum ts) (ZInject i e) = ZInject i (trivial (ts !! i) e)
trivial (CFix t) (ZRoll e) = ZRoll (trivial (beta (CFix t) t) e)
trivial t (ZApply a f x) = ZApply (trivialT a) (trivial (CFunc a t) f) (trivial a x)
trivial t (ZApplyT k c f s) = ZApplyT k (trivialT c) (trivial (CForall k c) f) (trivialT s)
trivial t (ZProject [r] p 0) = trivial (CProduct [r]) p
trivial t (ZProject ts p i) = ZProject (trivialT <$> ts) (trivial (CProduct ts) p) i
trivial t (ZCase [r] e [c]) = ZApply r (ZLambda (trivial t c)) (trivial (CSum [r]) e)
trivial t (ZCase ts e cs) = ZCase (trivialT <$> ts) (trivial (CSum ts) e) (trivial t <$> cs)
trivial t (ZUnroll r e) = ZUnroll (trivialT r) (trivial (CFix r) e)

reduceTrivial (t, e) = (trivialT t, trivial t e)








emptyLintEnv = ([], [])
lintPutType t (ts, ks) = (t:ts, ks)
lintPutKind k (ts, ks) = (fmap (shift 1) ts, k:ks)
lintGetType i (ts, ks) = ts !! i
lintGetKind i (ts, ks) = ks !! i

lintType (ZIndex i) r = do
	t <- lintGetType i <$> ask
	check (t == r) ("Type mismatch: " ++ show t ++ " /= " ++ show r)
lintType (ZRecur e) r = local (lintPutType r) (lintType e r)
lintType (ZLambda e) (CFunc a b) = local (lintPutType a) (lintType e b)
lintType (ZLambdaT e) (CForall k t) = local (lintPutKind k) (lintType e t)
lintType (ZTuple es) (CProduct ts) = do
	zipWithM lintType es ts
	return ()
lintType (ZInject i e) (CSum ts) = do
	check (i < length ts) ("Invalid constructor: " ++ show i ++ " >= " ++ show (length ts))
	lintType e (ts !! i)
lintType (ZRoll e) (CFix t) = lintType e (beta (CFix t) t)
lintType (ZApply a f x) r = do
	lintKind a Type
	lintType x a
	lintType f (CFunc a r)
lintType (ZApplyT k c f t) r = do
	lintKind (CForall k c) Type
	lintKind t k
	check (beta t c == r) ("Type mismatch: " ++ show (beta t c) ++ " /= " ++ show r)
	lintType f (CForall k c)
lintType (ZProject ts p i) r = do
	lintKinds ts
	check (i < length ts) ("Invalid index: " ++ show i ++ " >= " ++ show (length ts))
	check (ts !! i == r) ("Type mismatch: " ++ show (ts !! i) ++ " /= " ++ show r)
	lintType p (CProduct ts)
lintType (ZCase ts e ks) r = do
	lintKinds ts
	lintType e (CSum ts)
	zipWithM (\t k -> local (lintPutType t) (lintType k r)) ts ks
	return ()
lintType (ZUnroll t e) r = do
	check (beta (CFix t) t == r) ("Type mismatch: " ++ show (beta (CFix t) t) ++ " /= " ++ show r)
	lintType e (CFix t)
lintType e t = throwError ("Unexpected type: " ++ show e ++ " /: " ++ show t)

lintKind (CTIndex i) r = do
	k <- lintGetKind i <$> ask
	check (k == r) ("Kind mismatch: " ++ show k ++ " /= " ++ show r)
lintKind (CFunc a b) Type = lintKind a Type >> lintKind b Type
lintKind (CForall k t) Type = local (lintPutKind k) (lintKind t Type)
lintKind (CProduct ts) Type = lintKinds ts >> return ()
lintKind (CSum ts) Type = lintKinds ts >> return ()
lintKind (CFix t) Type = local (lintPutKind Type) (lintKind t Type)
lintKind (CTLambda t) (Arrow k h) = local (lintPutKind k) (lintKind t h)
lintKind (CTApply k c t) h = lintKind t k >> lintKind c (Arrow k h)
lintKind t k = throwError ("Unexpected kind: " ++ show t ++ " /: " ++ show k)

lintKinds = Trav.mapM (\t -> lintKind t Type)

lint :: (CType [], ZExpr) -> ReaderT ([CType []], [Kind]) (Either String) ()
lint (t, e) = lintKind t Type >> lintType e t

check prop err	| prop = return ()
		| otherwise = throwError err








{--

TYPE REIFICATION OMG THE HORROR:

repr : (k:[]) -> k -> *
repr <*> a = {a}
repr <s -> c> f = (a:s) -> repr <s> a -> repr <c a> (f a)

reify : (k:[]) -> (t:k) -> repr <k> t
reify <k> a = ra
reify <s -> t> (\a. e) = /\a. \ra. reify <t> e
reify <k> (<h>, c t) = (<repr <h> t>, (<repr <h -> k> c>, (reify <h -> k> c) [t]) (reify <h> t))
reify <*> (a -> b) = Func (reify <*> a, reify <*> b)
reify <*> (X ts) = Product (map (reify <*>) ts)
reify <*> (+ ts) = Sum (map (reify <*>) ts)
reify <*> (forall k c) = Forall (k, reify <k -> *> c)
reify <*> (exists k c) = Exists (k, reify <k -> *> c)
reify <*> (fix c) = Fix (reify <* -> *> c)

passT : (k:[]) -> k -> k
passT <k> a = a
passT <s -> t> (\a. e) = \a. passT <t> e
passT <k> (<h>, c t) = (<h>, (passT <h -> k> c) (passT <h> t))
passT <*> (a -> b) = passT <*> a -> passT <*> b
passT <*> (X ts) = X (map (passT <*>) ts)
passT <*> (+ ts) = + (map (passT <*>) ts)
passT <*> (forall k c) = forall k (\a. repr <k> a -> passT <*> (c a))
passT <*> (exists k c) = exists k (\a. repr <k> a, passT <*> (c a))
passT <*> (fix c) = fix (passT <* -> *> c)

pass : (a:*) -> a -> passT <*> a
pass [a] x = x
pass [a] (fix f) = fix (pass [a -> a] f)
pass [a -> b] (\x. e) = \x. pass [b] e
pass [X ts] (tuple es) = tuple (zipWith pass ts es)
pass [+ ts] (tag i e) = tag i (pass ts[i] e)
pass [forall k c] (/\a. e) = /\a. \ra. pass [c a] e
pass [exists k c] {t, e} = {passT <k> t, (reify <k> t, pass [c t] e)}
pass [fix c] (roll e) = roll (pass [c (fix c)] e)
pass [a] (<b>, f x) = ([passT <*> b], (pass [b -> a] f) (pass [b] x))
pass [a] (<X ts>, e.i) = (map (passT <*> ts), (pass [ts.i] e).i)
pass [a] (<+ ts>, e => ks) = (map (passT <*> ts), (pass [+ ts] e) => map zip.. ts ks)
pass [a] (<forall k c>, f t) = [repr <k> s] (<passT <*> (forall k c)> (pass [forall k c] f) s) (reify <k> t)
	where	s = passT <k> t
pass [a] (<exists k c>, let {a, x} = e1 in e2) = (passT <*> (exists k c), let {a, (ra, x)} = pass [exists k c] e1 in pass [a] e2)
pass [a] (<fix f>, unroll e) = (passT <*> (fix f), unroll (pass [fix f] e))

REPR a = <
  Func : (struct b, struct c) | a = b -> c
  Product : map struct ts | a = {ts}
  Sum : map struct ts | a = <ts>
  Forall : (repr <k -> *> f) | a = forall k f
  Exists : (repr <k -> *> f) | a = exists k f
  Fix : repr <* -> *> f | a = fix f
>


accumulate : (a:*) -> a -> stream (a -> a) -> stream a

--}

data RExpr v
	= RVar v
	| RRecur (RExpr v)
	| RLambda v (RExpr v)
	| RLambdaT v (RExpr v)
	| RTuple [RExpr v]
	| RInject Nat (RExpr v)
	| RRoll (RExpr v)
	| RReprFunc (RExpr v) (RExpr v)
	| RReprForall Kind (RExpr v)
	| RReprProduct [RExpr v]
	| RReprSum [RExpr v]
	| RReprFix (RExpr v)
	| RApply (RType v) (RExpr v) (RExpr v)
	| RApplyT (Kind, RType v) (RExpr v) (RType v)
	| RProject [RType v] (RExpr v) Nat
	| RCase [RType v] (RExpr v) [(v, RExpr v)]
	| RUnroll (RType v) (RExpr v)
	deriving (Show, Eq, Functor)

data RType v
	= RFunc (RType v) (RType v)
	| RForall Kind (RType v)
	| RProduct [RType v]
	| RSum [RType v]
	| RFix (RType v)
	| RRepr (RType v)
	| RTVar v
	| RTLambda v (RType v)
	| RTApply Kind (RType v) (RType v)
	deriving (Show, Eq, Functor)

repr :: Kind -> RType Nat -> State Nat (RType Nat)
repr Type t = return (RRepr t)
repr (Arrow k h) c = do
	a <- fresh
	ra <- repr k (RTVar a)
	rb <- repr h (RTApply k c (RTVar a))
	return (RForall k (RTLambda a (RFunc ra rb)))
	

reify :: Kind -> RType Nat -> ReaderT (Map Nat Nat) (State Nat) (RExpr Nat)
reify k (RTVar a) = RVar . (! a) <$> ask
reify Type (RFunc a b) = RReprFunc <$> reify Type a <*> reify Type b
reify Type (RProduct ts) = RReprProduct <$> Trav.mapM (reify Type) ts
reify Type (RSum ts) = RReprSum <$> Trav.mapM (reify Type) ts
reify Type (RForall k f) = RReprForall k <$> reify (Arrow k Type) f
reify Type (RFix f) = RReprFix <$> reify (Arrow Type Type) f
reify (Arrow k h) (RTLambda a t) = do
	a <- lift fresh
	ra <- lift fresh
	body <- local (Map.insert a ra) (reify h t)
	return (RLambdaT a (RLambda ra body))
reify k (RTApply h c t) = do
	refc <- reify (Arrow h k) c
	reft <- reify h t
	rept <- lift (repr h t)
	RForall _ repf <- lift (repr (Arrow h k) c)
	return (RApply rept (RApplyT (h, repf) refc t) reft)

passT :: Kind -> RType Nat -> State Nat (RType Nat)
passT k (RTVar a) = return (RTVar a)
passT Type (RFunc a b) = RFunc <$> passT Type a <*> passT Type b
passT Type (RProduct ts) = RProduct <$> Trav.mapM (passT Type) ts
passT Type (RSum ts) = RSum <$> Trav.mapM (passT Type) ts
passT Type (RForall k c) = do
	a <- fresh
	ra <- repr k (RTVar a)
	pc <- passT Type (RTApply k c (RTVar a))
	return (RForall k (RTLambda a (RFunc ra pc)))
passT Type (RFix c) = RFix <$> passT (Arrow Type Type) c
passT (Arrow k h) (RTLambda a t) = RTLambda a <$> passT h t
passT k (RTApply h c t) = RTApply h <$> passT (Arrow h k) c <*> passT h t

pass :: RExpr Nat -> ReaderT (Map Nat Nat) (State Nat) (RExpr Nat)
pass (RVar x) = return (RVar x)
pass (RRecur f) = RRecur <$> pass f
pass (RLambda x e) = RLambda x <$> pass e
pass (RTuple es) = RTuple <$> Trav.mapM pass es
pass (RInject i e) = RInject i <$> pass e
pass (RLambdaT a e) = do
	ra <- lift fresh
	pe <- local (Map.insert a ra) (pass e)
	return (RLambdaT a (RLambda ra pe))
pass (RRoll e) = RRoll <$> pass e
pass (RApply r f x) = RApply <$> lift (passT Type r) <*> pass f <*> pass x
pass (RProject ts e i) = RProject <$> Trav.mapM (lift . passT Type) ts <*> pass e <*> pure i
pass (RCase ts e ks) = RCase <$> Trav.mapM (lift . passT Type) ts <*> pass e <*> Trav.mapM cont ks
	where	cont (x, e) = (,) x <$> pass e
pass (RApplyT (k, c) f r) = do
	RForall _ rc <- lift (passT Type (RForall k c))
	rf <- pass f
	s <- lift (passT k r)
	reps <- lift (repr k s)
	refs <- reify k r
	return (RApply reps (RApplyT (k, rc) rf s) refs)
pass (RUnroll c e) = RUnroll <$> lift (passT (Arrow Type Type) c) <*> pass e
	
reification t e = (,) <$> passT Type t <*> runReaderT (pass e) Map.empty








instance Show Value where
	show (Clos env e) = "<" ++ show env ++ " : " ++ show e ++ ">"
	show (VTuple vs) = "{" ++ concat (intersperse ", " (show <$> vs)) ++ "}"
	show (VInject i e) = "[" ++ show i ++ " : " ++ show e ++ "]"
	show (VTRepr r) = show r
	
type Env = [Value]

data Value
	= Clos Env (RExpr Nat)
	| VTuple [Value]
	| VInject Nat Value
	| VTRepr Repr
	
data Repr
	= VFunc Repr Repr
	| VProduct [Repr]
	| VSum [Repr]
	| VForall Kind Value
	| VFix Value
	deriving (Show)




emptyEvalEnv = []
getValue i vs = vs !! i
putValue v vs = v:vs

valueOf (t, e) env = (t, evaluate e env)

evaluate e = runReader (eval e)

eval (RVar i) = getValue i <$> ask
eval (RRecur e) = eval e >>= \(Clos env body) -> mfix (\x -> return $ evaluate body (putValue x env))
eval (RLambda _ e) = Clos <$> ask <*> pure e
eval (RLambdaT _ e) = eval e
eval (RTuple es) = VTuple <$> Trav.mapM eval es
eval (RInject i e) = VInject i <$> eval e
eval (RRoll e) = eval e
eval (RReprFunc a b) = VTRepr <$> (VFunc <$> evalRepr a <*> evalRepr b)
eval (RReprForall k c) = VTRepr <$> (VForall k <$> eval c)
eval (RReprProduct ts) = VTRepr <$> (VProduct <$> Trav.mapM evalRepr ts)
eval (RReprSum ts) = VTRepr <$> (VSum <$> Trav.mapM evalRepr ts)
eval (RReprFix c) = VTRepr <$> (VFix <$> eval c)
eval (RApply s f x) = applyV <$> eval f <*> eval x
eval (RApplyT (k, c) f s) = eval f
eval (RProject ts p i) = project i <$> eval p
eval (RCase ts e ks) = eval e >>= caseof ks
eval (RUnroll r e) = eval e

applyV (Clos env e) v = evaluate e (putValue v env)
project i (VTuple vs) = vs !! i
caseof ks (VInject i v) = local (putValue v) (eval (snd (ks !! i)))
evalRepr e = eval e >>= \(VTRepr r) -> return r



{--

data RExpr v
	= RVar v
	| RRecur (RExpr v)
	| RLambda v (RExpr v)
	| RLambdaT v (RExpr v)
	| RTuple [RExpr v]
	| RInject Nat (RExpr v)
	| RRoll (RExpr v)
	| RReprFunc (RExpr v) (RExpr v)
	| RReprForall Kind (RExpr v)
	| RReprProduct [RExpr v]
	| RReprSum [RExpr v]
	| RReprFix (RExpr v)
	| RReprRepr (RExpr v)
	| RApply (RType v) (RExpr v) (RExpr v)
	| RApplyT (Kind, RType v) (RExpr v) (RType v)
	| RProject [RType v] (RExpr v) Nat
	| RCase [RType v] (RExpr v) [(v, RExpr v)]
	| RUnroll (RType v) (RExpr v)
	deriving (Show, Eq, Functor)




instance Show Value where
	show (Clos env e) = "<" ++ show env ++ " : " ++ show e ++ ">"
	show (ClosT env e) = "<" ++ show env ++ " : " ++ show e ++ ">"
	show (VTuple vs) = "{" ++ concat (intersperse ", " (show <$> vs)) ++ "}"
	show (VInject i e) = "[" ++ show i ++ " : " ++ show e ++ "]"
	show (VRoll e) = "(roll " ++ show e ++ ")"

instance Show TRepr where
	show (RFunc a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
	show (RForall k env t) = "(forall " ++ show k ++ " <" ++ show env ++ " : " ++ show t ++ ">)"
	show (RProduct ts) = "{" ++ concat (intersperse ", " (show <$> ts)) ++ "}"
	show (RSum ts) = "[" ++ concat (intersperse " | " (show <$> ts)) ++ "]"
	show (RFix env t) = "(fix <" ++ show env ++ " : " ++ show t ++ ">)"
	show (RClos env t) = "<" ++ show env ++ " : " ++ show t ++ ">"
	
type Env = ([Kind], [TRepr], [TRepr], [Value])

data Value
	= Clos Env ZExpr
	| ClosT Env ZExpr
	| VTuple [Value]
	| VInject Nat Value
	| VRoll Value

data TRepr
	= RFunc TRepr TRepr
	| RForall Kind Env (CType [])
	| RProduct [TRepr]
	| RSum [TRepr]
	| RFix Env (CType [])
	| RClos Env (CType [])

emptyEvalEnv = ([], [], [], [])
getValue i (ks, cs, ts, vs) = vs !! i
getCons i (ks, cs, ts, vs) = cs !! i
putValue rt v (ks, cs, ts, vs) = (ks, cs, rt:ts, v:vs)
putCons k c (ks, cs, ts, vs) = (k:ks, c:cs, ts, vs)

valueOf (t, e) env = (evaluateType Type t env, evaluate t e env)

evaluate t e = runReader (eval t e)

eval t (ZIndex i) = getValue i <$> ask
eval t (ZRecur e) = do
	rt <- evalType Type t
	mfix (\x -> local (putValue rt x) (eval t e))
eval (CFunc a b) (ZLambda e) = Clos <$> ask <*> pure e
eval (CForall k t) (ZLambdaT e) = ClosT <$> ask <*> pure e
eval (CProduct ts) (ZTuple es) = VTuple <$> zipWithM eval ts es
eval (CSum ts) (ZInject i e) = VInject i <$> eval (ts !! i) e
eval (CFix t) (ZRoll e) = VRoll <$> eval (beta (CFix t) t) e
eval t (ZApply s f x) = applyV <$> evalType Type s <*> pure t <*> eval (CFunc s t) f <*> eval s x
eval t (ZApplyT k e f s) = applyT k e <$> eval (CForall k e) f <*> evalType k s
eval t (ZProject ts p i) = project i <$> eval (CProduct ts) p
eval t (ZCase ts e ks) = eval (CSum ts) e >>= caseof ts t ks
eval t (ZUnroll r e) = unroll <$> eval (CFix r) e
eval t e = error ("Unexpected type: " ++ show t ++ " /: " ++ show e)

applyV s t (Clos env e) v = evaluate t e (putValue s v env)
applyT k t (ClosT env e) c = evaluate t e (putCons k c env)
project i (VTuple vs) = vs !! i
caseof ts r ks (VInject i v) = evalType Type (ts !! i) >>= \t -> local (putValue t v) (eval r (ks !! i))
unroll (VRoll v) = v

evaluateType k t = runReader (evalType k t)

evalType k (CTIndex i) = getCons i <$> ask
evalType Type (CFunc a b) = RFunc <$> evalType Type a <*> evalType Type b
evalType Type (CForall k e) = RForall k <$> ask <*> pure e
evalType Type (CProduct ts) = RProduct <$> Trav.mapM (evalType Type) ts
evalType Type (CSum ts) = RSum <$> Trav.mapM (evalType Type) ts
evalType Type (CFix e) = RFix <$> ask <*> pure e
evalType (Arrow k h) (CTLambda e) = RClos <$> ask <*> pure e
evalType k (CTApply h c t) = tApply h k <$> evalType (Arrow h k) c <*> evalType h t

tApply h k (RClos env e) c = evaluateType k e (putCons h c env)

--}


