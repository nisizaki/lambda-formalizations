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

inductive ParStep : Trm V → Trm V → Prop where
  | var (x : V) :
      ParStep (.var x) (.var x)
  | lam :
      ParStep U U' → ParStep (.lam x U) (.lam x U')
  | app :
      ParStep U U' → ParStep V V' → ParStep (.app U V) (.app U' V')
  | id :
      ParStep (.id : Trm V) .id
  | ext :
      ParStep U U' → ParStep V V' → ParStep (.ext U x V) (.ext U' x V')
  | lamComp :
      ParStep U U' → ParStep V V' → V ≠ .id → V' ≠ .id →
        ParStep (.comp (.lam x U) V) (.comp (.lam x U') V')
  | lamCompId :
      ParStep U U' → ParStep V .id → V ≠ .id →
        ParStep (.comp (.lam x U) V) (.lam x U')
  | varComp :
      ParStep W W' → not_ext W → not_ext W' → W ≠ .id → W' ≠ .id →
        ParStep (.comp (.var x) W) (.comp (.var x) W')
  | varCompOther :
      ParStep W W' → not_ext W → ¬ not_ext W' → W ≠ .id → W' ≠ .id →
        ParStep (.comp (.var x) W) (sigmaNormalize (.comp (.var x) W'))
  | varCompId :
      ParStep W .id → not_ext W → W ≠ .id →
        ParStep (.comp (.var x) W) (.var x)
  | beta1 :
      ParStep U U' → ParStep V V' →
        ParStep (.app (.lam x U) V)
          (sigmaNormalize (.comp U' (.ext V' x .id)))
  | beta2 :
      W ≠ .id → ParStep U U' → ParStep V V' → ParStep W W' →
        ParStep (.app (.comp (.lam x U) W) V)
          (sigmaNormalize (.comp U' (.ext V' x W')))

theorem ParStep.source_normal {U V : Trm V} (h : ParStep U V) : SigmaNormal U := by
  induction h with
  | var x => exact sigma_normal_TVar x
  | lam h ih => exact sigma_normal_lam ih
  | app hU hV ihU ihV => exact sigma_normal_app ihU ihV
  | id => exact sigma_normal_TId
  | ext hU hV ihU ihV => exact sigma_normal_ext ihU ihV
  | lamComp hU hV hVne hV'ne ihU ihV =>
      exact sigma_normal_TComp_lam_iff.mpr ⟨ihU, ihV, hVne⟩
  | lamCompId hU hV hVne ihU ihV =>
      exact sigma_normal_TComp_lam_iff.mpr ⟨ihU, ihV, hVne⟩
  | varComp hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact sigma_normal_TComp_var_iff.mpr ⟨ihW, hNotExt, hWne⟩
  | varCompOther hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact sigma_normal_TComp_var_iff.mpr ⟨ihW, hNotExt, hWne⟩
  | varCompId hW hNotExt hWne ihW =>
      exact sigma_normal_TComp_var_iff.mpr ⟨ihW, hNotExt, hWne⟩
  | beta1 hU hV ihU ihV =>
      exact sigma_normal_app (sigma_normal_lam ihU) ihV
  | beta2 hWne hU hV hW ihU ihV ihW =>
      exact sigma_normal_app (sigma_normal_TComp_lam_iff.mpr ⟨ihU, ihW, hWne⟩) ihV

theorem ParStep.target_normal {U V : Trm V} (h : ParStep U V) : SigmaNormal V := by
  induction h with
  | var x => exact sigma_normal_TVar x
  | lam h ih => exact sigma_normal_lam ih
  | app hU hV ihU ihV => exact sigma_normal_app ihU ihV
  | id => exact sigma_normal_TId
  | ext hU hV ihU ihV => exact sigma_normal_ext ihU ihV
  | lamComp hU hV hVne hV'ne ihU ihV =>
      exact sigma_normal_TComp_lam_iff.mpr ⟨ihU, ihV, hV'ne⟩
  | lamCompId hU hV hVne ihU ihV => exact sigma_normal_lam ihU
  | varComp hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact sigma_normal_TComp_var_iff.mpr ⟨ihW, hNotExt', hW'ne⟩
  | varCompOther hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact sigmaNormalize_normal _
  | varCompId hW hNotExt hWne ihW => exact sigma_normal_TVar _
  | beta1 hU hV ihU ihV => exact sigmaNormalize_normal _
  | beta2 hWne hU hV hW ihU ihV ihW => exact sigmaNormalize_normal _

theorem ParStep.normal {U V : Trm V} (h : ParStep U V) : SigmaNormal U ∧ SigmaNormal V :=
  ⟨h.source_normal, h.target_normal⟩

theorem ParStep.refl {M : Trm V} (normal : SigmaNormal M) : ParStep M M := by
  let P : Nat → Prop := fun n => ∀ M : Trm V, Trm.length M = n → SigmaNormal M → ParStep M M
  have aux : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro M length_eq normal
        cases M with
        | var x => exact ParStep.var x
        | lam x U =>
            have nU : SigmaNormal U := sigma_normal_TLam_iff.mp normal
            have lenU : Trm.length U < n := by
              rw [← length_eq]
              simp [Trm.length]
              nlinarith [Trm.length_pos U]
            exact ParStep.lam (ih (Trm.length U) lenU U rfl nU)
        | app U V =>
            have nUV := sigma_normal_TApp_iff.mp normal
            have lenU : Trm.length U < n := by
              rw [← length_eq]
              simp [Trm.length]
            have lenV : Trm.length V < n := by
              rw [← length_eq]
              simp [Trm.length]
            exact ParStep.app (ih (Trm.length U) lenU U rfl nUV.1)
              (ih (Trm.length V) lenV V rfl nUV.2)
        | id => exact ParStep.id
        | ext U x V =>
            have nUV := sigma_normal_TExt_iff.mp normal
            have lenU : Trm.length U < n := by
              rw [← length_eq]
              simp [Trm.length]
            have lenV : Trm.length V < n := by
              rw [← length_eq]
              simp [Trm.length]
            exact ParStep.ext (ih (Trm.length U) lenU U rfl nUV.1)
              (ih (Trm.length V) lenV V rfl nUV.2)
        | comp A B =>
            rcases sigma_normal_TComp_cases_for_par_refl normal with
              ⟨x, U, hA, nU, nB, hBne⟩ | ⟨x, hA, nB, hNotExt, hBne⟩
            · subst A
              have lenU : Trm.length U < n := by
                rw [← length_eq]
                simp [Trm.length]
                nlinarith [Trm.length_pos U, Trm.length_pos B]
              have lenB : Trm.length B < n := by
                rw [← length_eq]
                exact Trm.length_right_lt_comp (.lam x U) B
              exact ParStep.lamComp (ih (Trm.length U) lenU U rfl nU)
                (ih (Trm.length B) lenB B rfl nB) hBne hBne
            · subst A
              have lenB : Trm.length B < n := by
                rw [← length_eq]
                exact Trm.length_right_lt_comp (.var x) B
              exact ParStep.varComp (ih (Trm.length B) lenB B rfl nB)
                hNotExt hNotExt hBne hBne
  exact aux (Trm.length M) M rfl normal

end LambdaEnv
