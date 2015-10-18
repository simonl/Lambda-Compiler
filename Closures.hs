module Closures() where
import ExprFold
import Expressions
import Control.Applicative
import Control.Monad.Writer
import Data.Set as Set

data Annot v a = Annot { annot :: a, body :: Expression v (Annot v a) } deriving (Show)

instance (Monad m, Monoid w) => Applicative (WriterT w m) where
	pure = return
	(<*>) = ap

freeVars = fst . runWriter . foldExp freeVarFold
freeVarFold = ExprFold variable lambda tuple inject apply project caseOf force
	where	variable v = tag $ tell (Set.singleton v) >> return (Variable v)
		lambda v e = tag $ Lambda v <$> censor (Set.delete v) e
		tuple es = tag $ Tuple <$> sequence es
		inject i e = tag $ Inject i <$> e
		apply f x = tag $ Apply <$> f <*> x
		project i x = tag $ Project i <$> x
		caseOf s cs = tag $ Case <$> s <*> mapM onCont cs
			where	onCont (v, e) = (,) v <$> censor (Set.delete v) e
		force x = tag $ Force <$> x
		
		tag fe = fmap annotate (listen fe)
		annotate (e, free) = Annot { annot = free, body = e }

				
				