namespace LambdaEnv

inductive Trm (V : Type) where
  | var  : V → Trm V
  | lam  : V → Trm V → Trm V
  | app  : Trm V → Trm V → Trm V
  | id   : Trm V
  | ext  : Trm V → V → Trm V → Trm V
  | comp : Trm V → Trm V → Trm V
  deriving Repr, DecidableEq

#check Trm
#check Trm.var
#check Trm.lam
#check Trm.app
#check Trm.id
#check Trm.ext
#check Trm.comp

end LambdaEnv
