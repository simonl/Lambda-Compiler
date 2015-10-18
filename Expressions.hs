module Expressions(
	Expression(..),
	Value(..), Cont(..), Block(..),
	Nat, Ident) where

type Nat = Int
type Ident = Nat

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

data Value	= VLambda Ident Block
		| VTuple [Ident]
		| VInject Nat Ident
data Cont	= Current
		| Cont Ident Block
		| Assign Ident Block
data Block	= Let Cont Value
		| BApply Ident Ident Cont
		| BProject Nat Ident Cont
		| BCase Ident [Cont]
		| Return Cont Ident
	