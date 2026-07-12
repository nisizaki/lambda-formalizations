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

theorem ParStep.id_cases {T : Trm V} (h : ParStep .id T) : T = .id := by
  cases h
  rfl

theorem ParStep.var_cases {x : V} {T : Trm V} (h : ParStep (.var x) T) : T = .var x := by
  cases h
  rfl

theorem ParStep.ext_cases {U₁ U₂ T : Trm V} {x : V}
    (h : ParStep (.ext U₁ x U₂) T) :
    ∃ U₁' U₂', T = .ext U₁' x U₂' ∧ ParStep U₁ U₁' ∧ ParStep U₂ U₂' := by
  cases h with
  | ext h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem ParStep.lam_cases {U T : Trm V} {x : V}
    (h : ParStep (.lam x U) T) :
    ∃ U', T = .lam x U' ∧ ParStep U U' := by
  cases h with
  | lam h => exact ⟨_, rfl, h⟩

theorem ParStep.comp_lam_cases {U W T : Trm V} {x : V}
    (h : ParStep (.comp (.lam x U) W) T) :
    (∃ U' W', T = .comp (.lam x U') W' ∧ ParStep U U' ∧ ParStep W W' ∧
      W ≠ .id ∧ W' ≠ .id) ∨
    (∃ U', T = .lam x U' ∧ ParStep U U' ∧ ParStep W .id ∧ W ≠ .id) := by
  cases h with
  | lamComp pU pW Wne W'ne =>
      exact Or.inl ⟨_, _, rfl, pU, pW, Wne, W'ne⟩
  | lamCompId pU pW Wne =>
      exact Or.inr ⟨_, rfl, pU, pW, Wne⟩

theorem ParStep.comp_var_cases {W T : Trm V} {x : V}
    (h : ParStep (.comp (.var x) W) T) :
    (∃ W', T = .comp (.var x) W' ∧ ParStep W W' ∧ not_ext W ∧ not_ext W' ∧
      W ≠ .id ∧ W' ≠ .id) ∨
    (∃ W', T = sigmaNormalize (.comp (.var x) W') ∧ ParStep W W' ∧ not_ext W ∧
      ¬ not_ext W' ∧ W ≠ .id ∧ W' ≠ .id) ∨
    (T = .var x ∧ ParStep W .id ∧ not_ext W ∧ W ≠ .id) := by
  cases h with
  | varComp hW hNotExt hNotExt' hWne hW'ne =>
      exact Or.inl ⟨_, rfl, hW, hNotExt, hNotExt', hWne, hW'ne⟩
  | varCompOther hW hNotExt hNotExt' hWne hW'ne =>
      exact Or.inr (Or.inl ⟨_, rfl, hW, hNotExt, hNotExt', hWne, hW'ne⟩)
  | varCompId hW hNotExt hWne =>
      exact Or.inr (Or.inr ⟨rfl, hW, hNotExt, hWne⟩)

theorem ParStep.sigma_comp_id {E E' : Trm V} (h : ParStep E E') :
    ParStep (sigmaNormalize (.comp .id E)) (sigmaNormalize (.comp .id E')) := by
  rw [sigma_normalize_comp_id_left h.source_normal,
    sigma_normalize_comp_id_left h.target_normal]
  exact h

theorem ParStep.sigma_comp_ext {U₁ U₁' U₂ U₂' E E' : Trm V} {x : V}
    (h₁ : ParStep U₁ U₁') (h₂ : ParStep U₂ U₂') (hE : ParStep E E')
    (ih₁ : ParStep (sigmaNormalize (.comp U₁ E)) (sigmaNormalize (.comp U₁' E')))
    (ih₂ : ParStep (sigmaNormalize (.comp U₂ E)) (sigmaNormalize (.comp U₂' E')) ) :
    ParStep (sigmaNormalize (.comp (.ext U₁ x U₂) E))
      (sigmaNormalize (.comp (.ext U₁' x U₂') E')) := by
  rw [sigma_normalize_comp_ext (x := x) h₁.source_normal h₂.source_normal hE.source_normal,
    sigma_normalize_comp_ext (x := x) h₁.target_normal h₂.target_normal hE.target_normal]
  exact ParStep.ext ih₁ ih₂

theorem ParStep.sigma_comp_lam {U U' E E' : Trm V} {x : V}
    (hU : ParStep U U') (hE : ParStep E E') :
    ParStep (sigmaNormalize (.comp (.lam x U) E))
      (sigmaNormalize (.comp (.lam x U') E')) := by
  by_cases hE' : E' = .id
  · subst E'
    by_cases hEid : E = .id
    · subst E
      rw [sigma_normalize_comp_id_right (sigma_normal_lam hU.source_normal),
        sigma_normalize_comp_id_right (sigma_normal_lam hU.target_normal)]
      exact ParStep.lam hU
    · rw [sigma_normalize_comp_lam hU.source_normal hE.source_normal hEid,
        sigma_normalize_comp_id_right (sigma_normal_lam hU.target_normal)]
      exact ParStep.lamCompId hU hE hEid
  · by_cases hEne : E = .id
    · subst E
      exact False.elim (hE' hE.id_cases)
    · rw [sigma_normalize_comp_lam hU.source_normal hE.source_normal hEne,
        sigma_normalize_comp_lam hU.target_normal hE.target_normal hE']
      exact ParStep.lamComp hU hE hEne hE'

theorem ParStep.sigma_comp_app {U₁ U₁' U₂ U₂' E E' : Trm V}
    (h₁ : ParStep U₁ U₁') (h₂ : ParStep U₂ U₂') (hE : ParStep E E')
    (ih₁ : ParStep (sigmaNormalize (.comp U₁ E)) (sigmaNormalize (.comp U₁' E')))
    (ih₂ : ParStep (sigmaNormalize (.comp U₂ E)) (sigmaNormalize (.comp U₂' E')) ) :
    ParStep (sigmaNormalize (.comp (.app U₁ U₂) E))
      (sigmaNormalize (.comp (.app U₁' U₂') E')) := by
  rw [sigma_normalize_comp_app h₁.source_normal h₂.source_normal hE.source_normal,
    sigma_normalize_comp_app h₁.target_normal h₂.target_normal hE.target_normal]
  exact ParStep.app ih₁ ih₂

theorem ParStep.sigma_comp_var_not_ext {W W' : Trm V} {x : V}
    (h : ParStep W W') (hNotExt : not_ext W) :
    ParStep (sigmaNormalize (.comp (.var x) W))
      (sigmaNormalize (.comp (.var x) W')) := by
  have nW := h.source_normal
  have nVar : SigmaNormal (.var x : Trm V) := sigma_normal_TVar x
  by_cases hW' : W' = .id
  · subst W'
    by_cases hW : W = .id
    · subst W
      rw [sigma_normalize_comp_id_right nVar]
      exact ParStep.var x
    · rw [sigma_normalize_comp_var_not_ext nW hNotExt hW,
        sigma_normalize_comp_id_right nVar]
      exact ParStep.varCompId h hNotExt hW
  · by_cases hNotExt' : not_ext W'
    · by_cases hW : W = .id
      · subst W
        exact False.elim (hW' h.id_cases)
      · rw [sigma_normalize_comp_var_not_ext nW hNotExt hW,
          sigma_normalize_comp_var_not_ext h.target_normal hNotExt' hW']
        exact ParStep.varComp h hNotExt hNotExt' hW hW'
    · by_cases hW : W = .id
      · subst W
        exact False.elim (hW' h.id_cases)
      · rw [sigma_normalize_comp_var_not_ext nW hNotExt hW]
        exact ParStep.varCompOther h hNotExt hNotExt' hW hW'

theorem ParStep.sigma_comp_var_ext_same {M M' N N' : Trm V} {x : V}
    (hM : ParStep M M') (hN : ParStep N N') :
    ParStep (sigmaNormalize (.comp (.var x) (.ext M x N)))
      (sigmaNormalize (.comp (.var x) (.ext M' x N'))) := by
  rw [sigma_normalize_comp_var_ext_same x hM.source_normal hN.source_normal,
    sigma_normalize_comp_var_ext_same x hM.target_normal hN.target_normal]
  exact hM

theorem ParStep.sigma_comp_var_ext_diff {M M' N N' : Trm V} {x y : V}
    (hxy : x ≠ y) (hM : ParStep M M') (hN : ParStep N N')
    (ih : ParStep (sigmaNormalize (.comp (.var x) N))
      (sigmaNormalize (.comp (.var x) N'))) :
    ParStep (sigmaNormalize (.comp (.var x) (.ext M y N)))
      (sigmaNormalize (.comp (.var x) (.ext M' y N'))) := by
  rw [sigma_normalize_comp_var_ext_diff hxy hM.source_normal hN.source_normal,
    sigma_normalize_comp_var_ext_diff hxy hM.target_normal hN.target_normal]
  exact ih

theorem ParStep.sigma_comp_var {W W' : Trm V} {x : V}
    (h : ParStep W W') :
    ParStep (sigmaNormalize (.comp (.var x) W))
      (sigmaNormalize (.comp (.var x) W')) := by
  let P : Nat → Prop := fun n => ∀ W W' : Trm V, Trm.length W = n →
    ParStep W W' → ParStep (sigmaNormalize (.comp (.var x) W))
      (sigmaNormalize (.comp (.var x) W'))
  have aux : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W W' len hWW'
        cases W with
        | ext M y N =>
            rcases hWW'.ext_cases with ⟨M', N', rfl, hM, hN⟩
            by_cases hxy : x = y
            · subst y
              exact ParStep.sigma_comp_var_ext_same hM hN
            · have lenN : Trm.length N < n := by
                rw [← len]
                simp [Trm.length]
              exact ParStep.sigma_comp_var_ext_diff hxy hM hN
                (ih (Trm.length N) lenN N N' rfl hN)
        | var y => exact ParStep.sigma_comp_var_not_ext hWW' (by simp [not_ext])
        | lam y M => exact ParStep.sigma_comp_var_not_ext hWW' (by simp [not_ext])
        | app M N => exact ParStep.sigma_comp_var_not_ext hWW' (by simp [not_ext])
        | id => exact ParStep.sigma_comp_var_not_ext hWW' (by simp [not_ext])
        | comp M N => exact ParStep.sigma_comp_var_not_ext hWW' (by simp [not_ext])
  exact aux (Trm.length W) W W' rfl h

theorem ParStep.sigma_comp_lamcomp {U U' W W' E E' : Trm V} {x : V}
    (hU : ParStep U U') (hW : ParStep W W')
    (hWne : W ≠ .id) (hW'ne : W' ≠ .id) (hE : ParStep E E')
    (ih : ParStep (sigmaNormalize (.comp W E)) (sigmaNormalize (.comp W' E'))) :
    ParStep (sigmaNormalize (.comp (.comp (.lam x U) W) E))
      (sigmaNormalize (.comp (.comp (.lam x U') W') E')) := by
  have lhs : sigmaNormalize (.comp (.comp (.lam x U) W) E) =
      sigmaNormalize (.comp (.lam x U) (sigmaNormalize (.comp W E))) := by
    rw [sigma_normalize_comp_comp (sigma_normal_lam hU.source_normal) hW.source_normal hE.source_normal,
      ← sigmaNormalize_comp_right_normalize]
  have rhs : sigmaNormalize (.comp (.comp (.lam x U') W') E') =
      sigmaNormalize (.comp (.lam x U') (sigmaNormalize (.comp W' E'))) := by
    rw [sigma_normalize_comp_comp (sigma_normal_lam hU.target_normal) hW.target_normal hE.target_normal,
      ← sigmaNormalize_comp_right_normalize]
  rw [lhs, rhs]
  exact ParStep.sigma_comp_lam hU ih

theorem ParStep.sigma_comp_lamcomp_id {U U' W E E' : Trm V} {x : V}
    (hU : ParStep U U') (hW : ParStep W .id) (hWne : W ≠ .id)
    (hE : ParStep E E')
    (ih : ParStep (sigmaNormalize (.comp W E)) (sigmaNormalize (.comp .id E'))) :
    ParStep (sigmaNormalize (.comp (.comp (.lam x U) W) E))
      (sigmaNormalize (.comp (.lam x U') E')) := by
  have lhs : sigmaNormalize (.comp (.comp (.lam x U) W) E) =
      sigmaNormalize (.comp (.lam x U) (sigmaNormalize (.comp W E))) := by
    rw [sigma_normalize_comp_comp (sigma_normal_lam hU.source_normal) hW.source_normal hE.source_normal,
      ← sigmaNormalize_comp_right_normalize]
  have env : ParStep (sigmaNormalize (.comp W E)) E' := by
    rw [sigma_normalize_comp_id_left hE.target_normal] at ih
    exact ih
  rw [lhs]
  exact ParStep.sigma_comp_lam hU env

theorem ParStep.sigma_comp_varcomp {W W' E E' : Trm V} {x : V}
    (hW : ParStep W W') (hE : ParStep E E')
    (ih : ParStep (sigmaNormalize (.comp W E)) (sigmaNormalize (.comp W' E'))) :
    ParStep (sigmaNormalize (.comp (.comp (.var x) W) E))
      (sigmaNormalize (.comp (.comp (.var x) W') E')) := by
  have lhs : sigmaNormalize (.comp (.comp (.var x) W) E) =
      sigmaNormalize (.comp (.var x) (sigmaNormalize (.comp W E))) := by
    rw [sigma_normalize_comp_comp (sigma_normal_TVar x) hW.source_normal hE.source_normal,
      ← sigmaNormalize_comp_right_normalize]
  have rhs : sigmaNormalize (.comp (.comp (.var x) W') E') =
      sigmaNormalize (.comp (.var x) (sigmaNormalize (.comp W' E'))) := by
    rw [sigma_normalize_comp_comp (sigma_normal_TVar x) hW.target_normal hE.target_normal,
      ← sigmaNormalize_comp_right_normalize]
  rw [lhs, rhs]
  exact ParStep.sigma_comp_var ih

theorem ParStep.sigma_comp_beta1_id {U U' N N' : Trm V} {x : V}
    (hU : ParStep U U') (hN : ParStep N N') :
    ParStep (sigmaNormalize (.comp (.app (.lam x U) N) .id))
      (sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext N' x .id))) .id)) := by
  rw [sigma_normalize_comp_id_right (sigma_normal_app (sigma_normal_lam hU.source_normal) hN.source_normal),
    sigma_normalize_comp_id_right (sigmaNormalize_normal _)]
  exact ParStep.beta1 hU hN

theorem ParStep.sigma_comp_beta1 {U U' A A' E E' : Trm V} {x : V}
    (hU : ParStep U U') (hA : ParStep A A') (hE : ParStep E E')
    (ihLam : ParStep (sigmaNormalize (.comp (.lam x U) E))
      (sigmaNormalize (.comp (.lam x U') E')))
    (ihArg : ParStep (sigmaNormalize (.comp A E))
      (sigmaNormalize (.comp A' E'))) :
    ParStep (sigmaNormalize (.comp (.app (.lam x U) A) E))
      (sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext A' x .id))) E')) := by
  by_cases hEid : E = .id
  · subst E
    have hE'id : E' = .id := hE.id_cases
    subst E'
    exact ParStep.sigma_comp_beta1_id hU hA
  · by_cases hE'id : E' = .id
    · subst E'
      have hTarget : sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext A' x .id))) .id) =
          sigmaNormalize (.comp U' (.ext A' x .id)) :=
        sigma_normalize_comp_beta1_target_id hU.target_normal hA.target_normal
      rw [sigma_normalize_comp_app (sigma_normal_lam hU.source_normal) hA.source_normal hE.source_normal,
        sigma_normalize_comp_lam hU.source_normal hE.source_normal hEid, hTarget]
      have hArg' : sigmaNormalize (.comp A' .id) = A' :=
        sigma_normalize_comp_id_right hA.target_normal
      have argStep : ParStep (sigmaNormalize (.comp A E)) A' := by
        rw [← hArg']
        exact ihArg
      exact ParStep.beta2 hEid hU argStep hE
    · have lhs : sigmaNormalize (.comp (.app (.lam x U) A) E) =
        .app (.comp (.lam x U) E) (sigmaNormalize (.comp A E)) := by
        rw [sigma_normalize_comp_app (sigma_normal_lam hU.source_normal) hA.source_normal hE.source_normal,
          sigma_normalize_comp_lam hU.source_normal hE.source_normal hEid]
      have rhs : sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext A' x .id))) E') =
        sigmaNormalize (.comp U' (.ext (sigmaNormalize (.comp A' E')) x E')) :=
        sigma_normalize_comp_beta1_target_non_id hU.target_normal hA.target_normal hE.target_normal hE'id
      rw [lhs, rhs]
      exact ParStep.beta2 hEid hU ihArg hE

theorem ParStep.sigma_comp_beta2 {U U' W W' A A' E E' : Trm V} {x : V}
    (hWne : W ≠ .id) (hU : ParStep U U') (hW : ParStep W W')
    (hA : ParStep A A') (hE : ParStep E E')
    (ihFun : ParStep (sigmaNormalize (.comp (.comp (.lam x U) W) E))
      (sigmaNormalize (.comp (.comp (.lam x U') W') E')))
    (ihArg : ParStep (sigmaNormalize (.comp A E))
      (sigmaNormalize (.comp A' E'))) :
    ParStep (sigmaNormalize (.comp (.app (.comp (.lam x U) W) A) E))
      (sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext A' x W'))) E')) := by
  have nFun : SigmaNormal (.comp (.lam x U) W) :=
    sigma_normal_TComp_lam_iff.mpr ⟨hU.source_normal, hW.source_normal, hWne⟩
  have lhsApp : sigmaNormalize (.comp (.app (.comp (.lam x U) W) A) E) =
      .app (sigmaNormalize (.comp (.comp (.lam x U) W) E))
        (sigmaNormalize (.comp A E)) := by
    rw [sigma_normalize_comp_app nFun hA.source_normal hE.source_normal]
  have rhsBeta2 : sigmaNormalize (.comp (sigmaNormalize (.comp U' (.ext A' x W'))) E') =
      sigmaNormalize (.comp U' (.ext (sigmaNormalize (.comp A' E')) x
        (sigmaNormalize (.comp W' E')))) :=
    sigma_normalize_comp_beta2_target hU.target_normal hA.target_normal
      hW.target_normal hE.target_normal
  by_cases hF : sigmaNormalize (.comp W E) = .id
  · have srcFun : sigmaNormalize (.comp (.comp (.lam x U) W) E) = .lam x U :=
      sigma_normalize_lamcomp_env_id hU.source_normal hW.source_normal hE.source_normal hF
    by_cases hF' : sigmaNormalize (.comp W' E') = .id
    · have tgtFun : sigmaNormalize (.comp (.comp (.lam x U') W') E') = .lam x U' :=
        sigma_normalize_lamcomp_env_id hU.target_normal hW.target_normal hE.target_normal hF'
      rw [lhsApp, srcFun, rhsBeta2, hF']
      exact ParStep.beta1 hU ihArg
    · have tgtFun : sigmaNormalize (.comp (.comp (.lam x U') W') E') =
          .comp (.lam x U') (sigmaNormalize (.comp W' E')) :=
        sigma_normalize_lamcomp_env_non_id hU.target_normal hW.target_normal hE.target_normal hF'
      have impossible : ParStep (.lam x U) (.comp (.lam x U') (sigmaNormalize (.comp W' E'))) := by
        rw [← srcFun, ← tgtFun]
        exact ihFun
      rcases impossible.lam_cases with ⟨Z, hEq, _⟩
      cases hEq
  · have srcFun : sigmaNormalize (.comp (.comp (.lam x U) W) E) =
        .comp (.lam x U) (sigmaNormalize (.comp W E)) :=
      sigma_normalize_lamcomp_env_non_id hU.source_normal hW.source_normal hE.source_normal hF
    by_cases hF' : sigmaNormalize (.comp W' E') = .id
    · have tgtFun : sigmaNormalize (.comp (.comp (.lam x U') W') E') = .lam x U' :=
        sigma_normalize_lamcomp_env_id hU.target_normal hW.target_normal hE.target_normal hF'
      have funStep : ParStep (.comp (.lam x U) (sigmaNormalize (.comp W E))) (.lam x U') := by
        rw [← srcFun, ← tgtFun]
        exact ihFun
      rcases funStep.comp_lam_cases with ⟨_, _, hEq, _, hEnv, _, _⟩ | ⟨_, hEq, _, hEnv, _⟩
      · cases hEq
      · rw [lhsApp, srcFun, rhsBeta2, hF']
        exact ParStep.beta2 hF hU ihArg hEnv
    · have tgtFun : sigmaNormalize (.comp (.comp (.lam x U') W') E') =
          .comp (.lam x U') (sigmaNormalize (.comp W' E')) :=
        sigma_normalize_lamcomp_env_non_id hU.target_normal hW.target_normal hE.target_normal hF'
      have funStep : ParStep (.comp (.lam x U) (sigmaNormalize (.comp W E)))
          (.comp (.lam x U') (sigmaNormalize (.comp W' E'))) := by
        rw [← srcFun, ← tgtFun]
        exact ihFun
      rcases funStep.comp_lam_cases with ⟨_, _, hEq, _, hEnv, _, _⟩ | ⟨_, hEq, _, _, _⟩
      · cases hEq
        rw [lhsApp, srcFun, rhsBeta2]
        exact ParStep.beta2 hF hU ihArg hEnv
      · cases hEq

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
