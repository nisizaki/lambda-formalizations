import LambdaEnv.SigmaNormalization

namespace LambdaEnv

noncomputable def Trm.star : Trm V → Trm V
  | .id => .id
  | .var x => .var x
  | .lam x U => .lam x U.star
  | .ext U x V => .ext U.star x V.star
  | .app (.var x) U => .app (.var x) U.star
  | .app (.lam x U₁) U₂ =>
      sigmaNormalize (.comp U₁.star (.ext U₂.star x .id))
  | .app (.comp (.lam x U₁) U₂) U₃ =>
      sigmaNormalize (.comp U₁.star (.ext U₃.star x U₂.star))
  | .app U V => .app U.star V.star
  | .comp (.lam x U) V =>
      sigmaNormalize (.comp (.lam x U.star) V.star)
  | .comp (.var x) W =>
      sigmaNormalize (.comp (.var x) W.star)
  | .comp U V => sigmaNormalize (.comp U.star V.star)

theorem term_star_id : (Trm.id : Trm V).star = Trm.id := rfl

theorem term_star_var (x : V) : (Trm.var x : Trm V).star = Trm.var x := rfl

theorem term_star_ext (U E : Trm V) (x : V) :
    (Trm.ext U x E).star = Trm.ext U.star x E.star := rfl

theorem term_star_var_app (x : V) (U : Trm V) :
    (Trm.app (Trm.var x) U).star = Trm.app (Trm.var x) U.star := rfl

theorem term_star_beta1_app (x : V) (U₁ U₂ : Trm V) :
    (Trm.app (Trm.lam x U₁) U₂).star =
      sigmaNormalize (Trm.comp U₁.star (Trm.ext U₂.star x Trm.id)) := rfl

theorem term_star_beta2_app (x : V) (U₁ U₂ U₃ : Trm V) :
    (Trm.app (Trm.comp (Trm.lam x U₁) U₂) U₃).star =
      sigmaNormalize (Trm.comp U₁.star (Trm.ext U₃.star x U₂.star)) := rfl

theorem term_star_lam (x : V) (U : Trm V) :
    (Trm.lam x U).star = Trm.lam x U.star := rfl

theorem term_star_lam_comp (x : V) (U V : Trm V) :
    (Trm.comp (Trm.lam x U) V).star =
      sigmaNormalize (Trm.comp (Trm.lam x U.star) V.star) := rfl

theorem term_star_var_comp (x : V) (W : Trm V) :
    (Trm.comp (Trm.var x) W).star =
      sigmaNormalize (Trm.comp (Trm.var x) W.star) := rfl

theorem term_star_sigma_normal {U : Trm V} (normal : SigmaNormal U) :
    SigmaNormal U.star := by
  induction U with
  | var x => exact sigma_normal_TVar x
  | lam x U ih =>
      exact sigma_normal_lam (ih ((sigma_normal_TLam_iff).mp normal))
  | app U V ihU ihV =>
      have nU : SigmaNormal U := (sigma_normal_TApp_iff.mp normal).1
      have nV : SigmaNormal V := (sigma_normal_TApp_iff.mp normal).2
      have nUstar : SigmaNormal U.star := ihU nU
      have nVstar : SigmaNormal V.star := ihV nV
      cases U with
      | var x => exact sigma_normal_app (sigma_normal_TVar x) nVstar
      | lam x U => exact sigmaNormalize_normal _
      | app U₁ U₂ => exact sigma_normal_app nUstar nVstar
      | id => exact sigma_normal_app sigma_normal_TId nVstar
      | ext U₁ x U₂ => exact sigma_normal_app nUstar nVstar
      | comp U₁ U₂ =>
          cases U₁ with
          | lam x W => exact sigmaNormalize_normal _
          | var x => exact sigma_normal_app nUstar nVstar
          | app W X => exact sigma_normal_app nUstar nVstar
          | id => exact sigma_normal_app nUstar nVstar
          | ext W x X => exact sigma_normal_app nUstar nVstar
          | comp W X => exact sigma_normal_app nUstar nVstar
  | id => exact sigma_normal_TId
  | ext U x V ihU ihV =>
      exact sigma_normal_ext (ihU (sigma_normal_TExt_iff.mp normal).1)
        (ihV (sigma_normal_TExt_iff.mp normal).2)
  | comp U V ihU ihV =>
      cases U with
      | var x => exact sigmaNormalize_normal _
      | lam x W => exact sigmaNormalize_normal _
      | app W X => exact sigmaNormalize_normal _
      | id => exact sigmaNormalize_normal _
      | ext W x X => exact sigmaNormalize_normal _
      | comp W X => exact sigmaNormalize_normal _

theorem sigma_normalize_term_star_eq {U : Trm V} (normal : SigmaNormal U) :
    sigmaNormalize U.star = U.star :=
  sigmaNormalize_eq_of_normal (term_star_sigma_normal normal)

end LambdaEnv
