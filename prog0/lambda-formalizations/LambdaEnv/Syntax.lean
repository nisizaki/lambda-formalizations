import Mathlib

namespace LambdaEnv

inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq, Repr

end LambdaEnv
