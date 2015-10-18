module Expressions(
	Expression(..),
	Exp(..),
	ExprFold(..)) where
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Set as Set

type Nat = Int

update f = do
	x <- get
	modify f
	return x
fresh = update succ

data Expression v e
		= Variable v
		| Lambda v e
		| Tuple [e]
		| Inject Nat e
		| Apply e e
		| Project Nat e
		| Case e [(v, e)]
		| Force e
		deriving (Show)
	
data Exp v = Roll { unroll :: Expression v (Exp v) } deriving (Show)
data Annot v a = Annot { annot :: a, body :: Expression v (Annot v a) } deriving (Show)

data ExprFold v b = ExprFold {
	variable :: v -> b,
	lambda :: v -> b -> b,
	tuple :: [b] -> b,
	inject :: Nat -> b -> b,
	apply :: b -> b -> b,
	project :: Nat -> b -> b,
	caseOf :: b -> [(v, b)] -> b,
	force :: b -> b
}

emptyFold = ExprFold {
	variable = undefined,
	lambda = undefined,
	tuple = undefined,
	inject = undefined,
	apply = undefined,
	project = undefined,
	caseOf = undefined,
	force = undefined
}

foldExp cases = fold
	where	fold = reduce . unroll

		reduce (Variable v) = variable cases v
		reduce (Lambda v e) = lambda cases v (fold e)
		reduce (Tuple es) = tuple cases (fmap fold es)
		reduce (Inject tag e) = inject cases tag (fold e)
		reduce (Apply f x) = apply cases (fold f) (fold x)
		reduce (Project i x) = project cases i (fold x)
		reduce (Case x cs) = caseOf cases (fold x) (fmap onCont cs)
			where	onCont (v, e) = (v, fold e)
		reduce (Force x) = force cases (fold x)

