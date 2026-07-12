import LambdaEnv.Syntax

namespace LambdaEnv

inductive Step : Term → Term → Prop where
  | appLeft {M M' N : Term} :
      Step M M' →
      Step (.app M N) (.app M' N)

end LambdaEnv
