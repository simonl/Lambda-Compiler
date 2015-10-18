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

newtype Ident
	= Ident String
	deriving (Show, Eq, Ord)
	
newtype TIdent
	= TIdent String
	deriving (Show, Eq, Ord)
	
newtype Label
	= Label String
	deriving (Show, Eq, Ord)

data Kind
	= Type
	| Arrow Kind Kind

data Type
	= TVariable TIdent
	| TLambda TIdent Type
	| TApply Type Type
	
	| Func Type Type
	| Forall Kind Type
	| Product (Map Label Type)
	| Pair Type Type
	| Exists Kind Type
	| Sum (Map Label Type)
	
data Expr
	= Variable Ident
	
	| Lambda Ident Expr
	| LambdaT TIdent Expr
	| Record (Map Label Expr)
	| Cons Expr Expr
	| Pack Type Expr
	| Tag Label Expr
	
	| Apply Expr Expr
	| ApplyT Expr Type
	| Project Expr Label
	| Let Expr (Ident, Ident) Expr
	| Unpack Expr (TIdent, Ident) Expr
	| Case Expr (Map Label (Ident, Expr))
	
data Repr
	= RTLambda (Map TIdent Repr) TIdent Type
	
	| RFunc Repr Repr
	| RForall Kind Repr
	| RProduct (Map Label Repr)
	| RPair Repr Repr
	| RExists Kind Repr
	| RSum (Map Label Repr)

data Value
	= VLambda (Map Ident Value) (Map TIdent Repr) Ident Expr
	| VLambdaT (Map Ident Value) (Map TIdent Repr) TIdent Expr
	| VRecord (Map Label Value)
	| VCons Value Value
	| VPack Repr Value
	| VTag Label Value
	
eval (Variable x) vs ts = vs ! x

eval (Lambda x e) vs ts = VLambda vs ts x e
eval (LambdaT a e) vs ts = VLambdaT vs ts a e
eval (Record es) vs ts = VRecord ((\e -> eval e vs ts) <$> es)
eval (Cons l r) vs ts = VCons (eval l vs ts) (eval r vs ts)
eval (Pack t e) vs ts = VPack (repr t ts) (eval e vs ts)
eval (Tag l e) vs ts = VTag l (eval e vs ts)

eval (Apply f x) vs ts = apply (eval f vs ts) (eval x vs ts)
eval (ApplyT f t) vs ts = applyT (eval f vs ts) (repr t ts)
eval (Project r l) vs ts = project (eval r vs ts) l
eval (Let e (x, y) k) vs ts = letv (eval e vs ts) (x, y) (vs, ts, k)
eval (Unpack e (a, x) k) vs ts = unpack (eval e vs ts) (a, x) (vs, ts, k)
eval (Case e ks) vs ts = caseof (eval e vs ts) (vs, ts, ks)

repr (TVariable a) ts = ts ! a
repr (TLambda a t) ts = RTLambda ts a t
repr (TApply f t) ts = tapply (repr f ts) (repr t ts)

repr (Func a b) ts = RFunc (repr a ts) (repr b ts)
repr (Forall k f) ts = RForall k (repr f ts)
repr (Product as) ts = RProduct ((\t -> repr t ts) <$> as)
repr (Pair a b) ts = RPair (repr a ts) (repr b ts)
repr (Exists k f) ts = RExists k (repr f ts)
repr (Sum as) ts = RSum ((\t -> repr t ts) <$> as)

apply (VLambda vs ts x e) v = eval e (Map.insert x v vs) ts
applyT (VLambdaT vs ts a e) t = eval e vs (Map.insert a t ts)
project (VRecord vs) l = vs ! l
letv (VCons l r) (x, y) (vs, ts, k) = eval k (Map.insert y r (Map.insert x l vs)) ts
unpack (VPack t v) (a, x) (vs, ts, k) = eval k (Map.insert x v vs) (Map.insert a t ts)
caseof (VTag l v) (vs, ts, ks) = let (x, k) = (ks ! l) in eval k (Map.insert x v vs) ts

tapply (RTLambda ts a t) r = repr t (Map.insert a r ts)


{--



eval : (a:*) -> (b:*) -> {a -> b} -> a -> b

eval ctx type (Index i) env cont = cont (lookup ctx[0].length env[0] i)
eval ctx (Func a b) (Lambda e) env cont = cont (ctx, env, e)
eval ctx (Forall k f) (TLambda e) env cont = cont (ctx, env, e)
eval ctx (Product n ts) (Tuples es) env cont =
	let mem = malloc n; rec n ts es (malloc n)
	where	rec 0 () () () = cont mem
		rec (1+n) (t, ts) (e, es) (m, ms) = eval ctx t e env (\v -> m := v; rec n ts es ms)
eval ctx (Pair a b) (Pair ea eb) env cont = eval ctx a ea env (\va -> eval ctx b ab env (\vb -> cont (va, vb)))
eval ctx (Exists k f) (Pack t e) env cont = evalT ctx[1] k t env[1] (\r -> apply f r (\lr -> eval ctx lr e env (\v -> cont (r, v))))
eval ctx (Sum n ts) (Tag i e) env cont = eval ctx (ts !! i) e env (\v -> cont (i, v))
eval ctx _ (Apply (Func a b) f x) env cont = eval ctx (Func a b) f env (\g -> eval ctx a x env (\v -> apply g v cont)))
eval ctx _ (TApply (Forall k f) c t) env cont = eval ctx (Forall k f) c env (\g -> evalT ctx[1] k t env[1] (\r -> tapply g r cont))
eval ctx _ (Project (Product n ts) r i) env cont = eval ctx (Product n ts) r env (\vs -> cont (vs !! i))
eval ctx _ (Let (Pair a b) e k) env cont = eval ctx (Pair a b) e env (\p -> let p k (ctx, env, cont))
eval ctx _ (Unpack (Exists k f) e c) env cont = eval ctx (Exists k f) e env (\p -> unpack p k (ctx, env, cont))
eval ctx _ (Case (Sum n ts) e ks) env cont = eval ctx (Sum n ts) e env (\(i, v) -> apply (ctx, env, ks !! i) v cont)




EXTENSIONS/AXIOMS =>

equality : {
  (==) : * -> * -> *
  refl : (a:*) -> (a == a)
  convert : (a:*) -> (b:*) -> (a == b) -> (f:* -> *) -> f a -> f b
}

reflexion : {
  test : (a:*) -> (b:*) -> maybe (a == b)
}

imperative : {
  ref : * -> *
  (&_) : (a:*) -> a -> ref a
  (*_) : (a:*) -> ref a -> a
  (:=) : (a:*) -> (ref a, a) -> ()
}

laziness : {
  lazy : +* -> *
  delay : (a:*) -> (() -> a) -> lazy a
  force : (a:*) -> lazy a -> a
}

least : {
  fix : +(+* -> *) -> *
  iso : (f:+* -> *) -> fix f == f (fix f)
  cata : (f:+* -> *) -> fix f -> (a:*) -> (f a -> a) -> a
}

greatest : {
  fix : +(+* -> *) -> *
  iso : (f:+* -> *) -> fix f == lazy (f (fix f))
  ana : (f:+* -> *) -> (a:*, a, a -> f a) -> fix f
}

unsafe : {
  fix : (* -> *) -> *
  recur : (a:*) -> (a -> a) -> a
}




list : +* -> *
list a = least.fix (\r. Nil | Cons (a, r))

foldr : (a:*) -> list a -> (b:*) -> (a -> b -> b) -> b -> b
foldr [a] xs [b] f z = least.cata [\r. Nil | Cons (a, r)] xs [b] reduce
	where	reduce : listF a b -> b
		reduce Nil = z
		reduce (Cons (x, r)) = f x r

nat : *
nat = least.fix (\r. Zero | Succ r)

iterate : nat -> (b:*) -> (b -> b) -> b -> b
iterate n [b] f z = least.cata [\r. Zero | Succ r] n [b] reduce
	where	reduce : natF b -> b
		reduce Zero = z
		reduce (Succ r) = f r

maybe : +* -> *
maybe a = Nothing | Just a

tree : +* -> *
tree a = least.fix (\r. Empty | Branch (a, r, r))

stream : +* -> *
stream a = greatest.fix (\r. (a, r))

sometime : +* -> *
sometime a = greatest.fix (\r. Now a | Later r)

never : (a:*) -> sometime a
never [a] = ana [\r. r] ({}, {}, \x. x)

repeat : (a:*) -> a -> stream a
repeat [a] x = ana [\r. (a, r)] (a, x \x. (x, x))

--}

