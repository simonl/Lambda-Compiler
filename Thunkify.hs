module Thunkify(thunkify) where
import ExprFold
import Expressions

thunkify = foldExp thunkFold
thunkFold = ExprFold variable lambda tuple inject apply project caseOf force
	where	variable x = Roll $ Force $ Roll $ Variable x
		lambda v te = Roll $ Lambda v te
		tuple tes = Roll $ Tuple $ fmap delay tes
		inject i te = Roll $ Inject i $ delay te
		apply tf tx = Roll $ Apply tf $ delay tx
		project i tx = Roll $ Force $ Roll $ Project i tx
		caseOf ts cs = Roll $ Case ts $ cs
		force tx = error "Cannot introduce thunks more than once"

delay = match . unroll 
	where	match (Force x) = x
		match (Variable x) = Roll $ value $ Roll $ Variable x
		match (Lambda v e) = Roll $ value $ Roll $ Lambda v e
		match (Tuple es) = Roll $ thunk $ Roll $ Tuple es
		match (Inject i e) = Roll $ thunk $ Roll $ Inject i e
		match (Apply f x) = Roll $ thunk $ Roll $ Apply f x
		match (Project i x) = Roll $ Project i x
		match (Case s cs) = Roll $ thunk $ Roll $ Case s cs

		value = Inject 0
		thunk = Inject 1 . Roll . Lambda "_"
