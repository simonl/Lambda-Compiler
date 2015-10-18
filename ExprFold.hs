module ExprFold(
	ExprFold(..),
	Exp(..),
	foldExp) where
import Expressions

data Exp v = Roll { unroll :: Expression v (Exp v) } deriving (Show)

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


