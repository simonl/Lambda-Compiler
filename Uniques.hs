module Uniques(uniques) where
import Expressions
import ExprFold
import Control.Applicative
import Control.Monad.State


update f = do
	x <- get
	modify f
	return x
fresh = update succ

instance (Monad m) => Applicative (StateT s m) where
	pure = return
	(<*>) = ap


uniques e = runStateT (foldExp uniqFold e []) 0

uniqFold = ExprFold variable lambda tuple inject apply project caseOf force
	where	variable v env = Roll . Variable <$> lift (lookup v env)
		lambda v ue env = binding v ue env >>= \(id, e) -> return $ Roll $ Lambda id e
		tuple ues env = Roll . Tuple <$> mapM (\ue -> ue env) ues
		inject tag ue env = Roll . Inject tag <$> ue env
		apply uf ux env = Roll <$> (Apply <$> uf env <*> ux env)
		project i ux env = Roll . Project i <$> ux env
		caseOf ux cs env = Roll <$> (Case <$> ux env <*> mapM onCont cs)
			where	onCont (v, ue) = binding v ue env
		force ux env = Roll . Force <$> ux env
		
		binding v ue env = fresh >>= \id -> (,) id <$> (ue $ (v, id):env)
