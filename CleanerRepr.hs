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
	deriving (Show)
 
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
 	| Repr Type
	deriving (Show)
 	
 data Expr
 	= Variable Ident
 	
 	| Lambda Ident Expr
 	| LambdaT TIdent Expr
 	| Record (Map Label Expr)
 	| Cons Expr Expr
 	| Pack Type Expr
 	| Tag Label Expr
 	
	| IFunc Expr Expr
	| IForall Kind Expr
	| IProduct (Map Label Expr)
	| IPair Expr Expr
	| IExists Kind Expr
 	| ISum (Map Label Expr)
 	| IRepr
 	
 	| Apply Expr Expr
 	| ApplyT Expr Type
 	| Project Expr Label
 	| Let Expr (Ident, Ident) Expr
 	| Unpack Expr (TIdent, Ident) Expr
 	| Case Expr (Map Label (Ident, Expr))
	deriving (Show)
 
 data Repr
 	= RFunc Repr Repr
 	| RForall Kind Value
 	| RProduct (Map Label Repr)
 	| RPair Repr Repr
 	| RExists Kind Value
 	| RSum (Map Label Repr)
 	| RRepr
	deriving (Show)
 
 data Value
 	= VLambda (Map Ident Value) Ident Expr
 	| VRecord (Map Label Value)
 	| VCons Value Value
 	| VTag Label Value
 	| VRepr Repr
	deriving (Show)
 	
 eval (Variable x) vs = vs ! x
 
 eval (Lambda x e) vs = VLambda vs x e
 eval (LambdaT a e) vs = eval e vs
 eval (Record es) vs = VRecord ((\e -> eval e vs) <$> es)
 eval (Cons l r) vs = VCons (eval l vs) (eval r vs)
 eval (Pack t e) vs = eval e vs
 eval (Tag l e) vs = VTag l (eval e vs)
 
 eval (IFunc a b) vs = VRepr $ RFunc (repr $ eval a vs) (repr $ eval b vs)
 eval (IForall k f) vs = VRepr $ RForall k (eval f vs)
 eval (IProduct as) vs = VRepr $ RProduct ((\t -> repr $ eval t vs) <$> as)
 eval (IPair a b) vs = VRepr $ RPair (repr $ eval a vs) (repr $ eval b vs)
 eval (IExists k f) vs = VRepr $ RExists k (eval f vs)
 eval (ISum as) vs = VRepr $ RSum ((\t -> repr $ eval t vs) <$> as)
 eval IRepr vs = VRepr RRepr
 
 eval (Apply f x) vs = apply (eval f vs) (eval x vs)
 eval (ApplyT f t) vs = eval f vs
 eval (Project r l) vs = project (eval r vs) l
 eval (Let e (x, y) k) vs = letc (eval e vs) (x, y) (vs, k)
 eval (Unpack e (a, x) k) vs = letv (eval e vs) x (vs, k)
 eval (Case e ks) vs = caseof (eval e vs) (vs, ks)
 
 repr (VRepr r) = r
 
 apply (VLambda vs x e) v = eval e (Map.insert x v vs)
 project (VRecord vs) l = vs ! l
 letc (VCons l r) (x, y) (vs, k) = eval k (Map.insert y r (Map.insert x l vs))
 letv v x (vs, k) = eval k (Map.insert x v vs)
 caseof (VTag l v) (vs, ks) = let (x, k) = (ks ! l) in eval k (Map.insert x v vs)
 
 
 
