import Control.Monad

data Expr
	= Index Int
	| Lambda Type Expr
	| Tuple [Expr]
	| Tag Int Expr [Type]
	| TLambda Kind Expr
	| Pack Type Expr Type
	| Apply Expr Expr
	| Project Expr Int
	| Case Expr [Expr]
	| TApply Expr Type
	| Unpack Expr Expr
	| Annot Expr Type
	deriving (Show, Eq)

data Type
	= Func Type Type
	| Product [Type]
	| Sum [Type]
	| Forall Kind Type
	| Exists Kind Type
	| IndexT Int
	| LambdaT Kind Type
	| ApplyT Type Type
	deriving (Show, Eq)

data Kind
	= Type
	| ArrowK Kind Kind
	deriving (Show, Eq)



-- Expr -> (Int, Int) -> Bool
scoped (Index i) (vs, _) = i < vs
scoped (Lambda t e) (vs, ts) = scopedT t ts && scoped e (vs+1, ts)
scoped (Tuple es) env = all (\e -> scoped e env) es
scoped (Tag _ e ann) (vs, ts) = scoped e (vs, ts) && all (\t -> scopedT t ts) ann
scoped (TLambda _ e) (vs, ts) = scoped e (vs, ts+1)
scoped (Pack rt e t) (vs, ts) = scopedT rt ts && scoped e (vs, ts) && scopedT t (ts+1) 
scoped (Apply f x) env = scoped f env && scoped x env
scoped (Project e _) env = scoped e env
scoped (Case e cs) (vs, ts) = scoped e (vs, ts) && all (\c -> scoped c (vs+1, ts)) cs
scoped (TApply f t) (vs, ts) = scoped f (vs, ts) && scopedT t ts
scoped (Unpack e1 e2) (vs, ts) = scoped e1 (vs, ts) && scoped e2 (vs+1, ts+1)
scoped (Annot e t) (vs, ts) = scoped e (vs, ts) && scopedT t ts

scopedT (Func a b) ts = scopedT a ts && scopedT b ts
scopedT (Product as) ts = all (\a -> scopedT a ts) as
scopedT (Sum as) ts = all (\a -> scopedT a ts) as
scopedT (Forall _ t) ts = scopedT t (ts+1)
scopedT (Exists _ t) ts = scopedT t (ts+1)
scopedT (IndexT i) ts = i < ts
scopedT (LambdaT _ t) ts = scopedT t (ts+1)
scopedT (ApplyT c t) ts = scopedT c ts && scopedT t ts




synon ts e = fold e 0
	where	fold (Index i) _ = Index i
		fold (Lambda t e) depth = Lambda (foldT t depth) (fold e depth)
		fold (Tuple es) depth = Tuple (fmap (\e -> fold e depth) es)
		fold (Tag i e ts) depth = Tag i (fold e depth) (fmap (\t -> foldT t depth) ts)
		fold (TLambda k e) depth = TLambda k (fold e (depth+1))
		fold (Pack rt e t) depth = Pack (foldT rt depth) (fold e depth) (foldT t (depth+1))
		fold (Apply f x) depth = Apply (fold f depth) (fold x depth)
		fold (Project e i) depth = Project (fold e depth) i
		fold (Case e cs) depth = Case (fold e depth) (fmap (\c -> fold c depth) cs)
		fold (TApply f t) depth = TApply (fold f depth) (foldT t depth)
		fold (Unpack e1 e2) depth = Unpack (fold e1 depth) (fold e2 (depth+1))
		fold (Annot e t) depth = Annot (fold e depth) (foldT t depth)

		foldT (Func a b) depth = Func (foldT a depth) (foldT b depth)
		foldT (Product ts) depth = Product (fmap (\t -> foldT t depth) ts)
		foldT (Sum ts) depth = Sum (fmap (\t -> foldT t depth) ts)
		foldT (Forall k t) depth = Forall k (foldT t (depth+1))
		foldT (Exists k t) depth = Exists k (foldT t (depth+1))
		foldT (IndexT i) depth	| i < depth = IndexT i
					| otherwise = ts !! (i - depth)
		foldT (LambdaT k t) depth = LambdaT k (foldT t (depth+1))
		foldT (ApplyT c t) depth = ApplyT (foldT c depth) (foldT t depth)
		
		

typeOf (Index i) (ts, _) = return (ts !! i)
typeOf (Lambda t e) (ts, ks) = do
	Type <- kindOf t ks
	let t' = normalize t
	ret <- typeOf e (t':ts, ks)
	return (Func t' ret)
typeOf (Tuple es) env = do
	ts <- mapM (\e -> typeOf e env) es
	return (Product ts)
typeOf (Tag i e ann) (ts, ks) = do
	ks <- mapM (\t -> kindOf t ks) ann
	guard (all (== Type) ks)
	guard (i < length ann)
	let ann' = fmap normalize ann
	te <- typeOf e (ts, ks)
	guard (te == ann' !! i)
	return (Sum ann')
typeOf (TLambda k e) (ts, ks) = do
	ret <- typeOf e (fmap (shift 1) ts, k:ks)
	return (Forall k ret)
typeOf (Pack rt e t) (ts, ks) = do
	k <- kindOf rt ks
	te <- typeOf e (ts, ks)
	let t' = normalize (beta (normalize rt) (normalize t))
	guard (te == t')
	return (Exists k t')
typeOf (Apply f x) env = do
	Func a b <- typeOf f env
	c <- typeOf x env
	guard (a == c)
	return b
typeOf (Project e i) env = do
	Product ts <- typeOf e env
	guard (i < length ts)
	return (ts !! i)
typeOf (Case e cs) (ts, ks) = do
	Sum as <- typeOf e (ts, ks)
	guard (length as == length cs)
	(r:rs) <- mapM (\(i, c) -> typeOf c (as !! i : ts, ks)) (zip [0..] cs)
	guard (all (== r) rs)
	return r
typeOf (TApply f t) (ts, ks) = do
	Forall k te <- typeOf f (ts, ks)
	kt <- kindOf t ks
	guard (kt == k)
	return (normalize (beta (normalize t) te))
typeOf (Unpack e1 e2) env = do
	Exists k te <- typeOf e1 env
	Forall _ (Func _ ret) <- typeOf (TLambda k (Lambda te e2)) env
	guard (noEscape ret)
	return (shift (-1) ret)
typeOf (Annot e t) env = do
	r <- typeOf e env
	guard (r == t)
	return t
	
	

kindOf (Func a b) env = do
	Type <- kindOf a env
	Type <- kindOf b env
	return Type
kindOf (Product ts) env = do
	ks <- mapM (\t -> kindOf t env) ts
	guard (all (== Type) ks)
	return Type
kindOf (Sum ts) env = do
	ks <- mapM (\t -> kindOf t env) ts
	guard (all (== Type) ks)
	return Type
kindOf (Forall k t) env = do
	Type <- kindOf t (k:env)
	return Type
kindOf (Exists k t) env = do
	Type <- kindOf t (k:env)
	return Type
kindOf (IndexT i) env = return (env !! i)
kindOf (LambdaT k t) env = do
	kr <- kindOf t (k:env)
	return (ArrowK k kr)
kindOf (ApplyT c t) env = do
	ArrowK a b <- kindOf c env
	c <- kindOf t env
	guard (a == c)
	return b

normalize (Func a b) = Func (normalize a) (normalize b)
normalize (Product ts) = Product (fmap normalize ts)
normalize (Sum ts) = Sum (fmap normalize ts)
normalize (Forall k t) = Forall k (normalize t)
normalize (Exists k t) = Exists k (normalize t)
normalize (IndexT i) = IndexT i
normalize (LambdaT k t) = LambdaT k (normalize t)
normalize (ApplyT c t) = apply (normalize c) (normalize t)

apply (LambdaT _ t) v = normalize (beta v t)
apply c v = ApplyT c v


shift n t = fold t 0
	where	fold (Func a b) depth = Func (fold a depth) (fold b depth)
		fold (Product ts) depth = Product (fmap (\t -> fold t depth) ts)
		fold (Sum ts) depth = Sum (fmap (\t -> fold t depth) ts)
		fold (Forall k t) depth = Forall k (fold t (depth+1))
		fold (Exists k t) depth = Exists k (fold t (depth+1))
		fold (LambdaT k t) depth = LambdaT k (fold t (depth+1))
		fold (ApplyT c t) depth = ApplyT (fold c depth) (fold t depth)
		fold (IndexT i) depth	| i < depth = IndexT i
					| otherwise = IndexT (i + n)

beta v t = fold t 0
	where	fold (Func a b) depth = Func (fold a depth) (fold b depth)
		fold (Product ts) depth = Product (fmap (\t -> fold t depth) ts)
		fold (Sum ts) depth = Sum (fmap (\t -> fold t depth) ts)
		fold (Forall k t) depth = Forall k (fold t (depth+1))
		fold (Exists k t) depth = Exists k (fold t (depth+1))
		fold (LambdaT k t) depth = LambdaT k (fold t (depth+1))
		fold (ApplyT c t) depth = ApplyT (fold c depth) (fold t depth)
		fold (IndexT i) depth	| i < depth = IndexT i
					| i > depth = IndexT (i+1)
					| otherwise = shift depth v

noEscape t = fold t 0
	where	fold (Func a b) depth = fold a depth && fold b depth
		fold (Product ts) depth = all (\t -> fold t depth) ts
		fold (Sum ts) depth = all (\t -> fold t depth) ts
		fold (Forall _ t) depth = fold t (depth+1)
		fold (Exists _ t) depth = fold t (depth+1)
		fold (LambdaT _ t) depth = fold t (depth+1)
		fold (ApplyT c t) depth = fold c depth && fold t depth
		fold (IndexT i) depth	= i /= depth


