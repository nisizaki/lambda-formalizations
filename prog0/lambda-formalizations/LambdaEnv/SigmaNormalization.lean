import LambdaEnv.Reduction

namespace LambdaEnv

open Relation

def NormalFormFor (r : α → α → Prop) (M N : α) : Prop :=
  Relation.ReflTransGen r M N ∧ ∀ N', ¬ r N N'

def NormalFor (r : α → α → Prop) (M : α) : Prop :=
  ∀ N, ¬ r M N

def SigmaNormal (M : Trm V) : Prop :=
  NormalFor SigmaStep M

def SigmaNormalForm (M N : Trm V) : Prop :=
  NormalFormFor SigmaStep M N

def Confluent (r : α → α → Prop) : Prop :=
  ∀ ⦃M N L⦄, Relation.ReflTransGen r M N → Relation.ReflTransGen r M L →
    Joinable r N L

def not_ext : Trm V → Prop
  | .ext _ _ _ => False
  | _ => True

theorem no_step_reflTransGen_eq {r : α → α → Prop} {x y : α}
    (steps : Relation.ReflTransGen r x y) (nf : ∀ z, ¬ r x z) :
    x = y := by
  induction steps with
  | refl => rfl
  | tail steps step ih =>
      subst ih
      exact False.elim (nf _ step)

theorem normalFormFor_exists_of_wellFounded {r : α → α → Prop}
    (wf : WellFounded fun N M => r M N) (M : α) :
    ∃ N, NormalFormFor r M N := by
  refine @WellFounded.induction α (fun N M => r M N) wf
    (fun M => ∃ N, NormalFormFor r M N) M ?_
  intro M ih
  by_cases hstep : ∃ N, r M N
  · rcases hstep with ⟨N, hMN⟩
    rcases ih N hMN with ⟨L, hNL, hnf⟩
    exact ⟨L, Relation.ReflTransGen.head hMN hNL, hnf⟩
  · exact ⟨M, Relation.ReflTransGen.refl, by
      intro N hMN
      exact hstep ⟨N, hMN⟩⟩

theorem SigmaNormalForm.exists (M : Trm V) :
    ∃ N, SigmaNormalForm M N :=
  normalFormFor_exists_of_wellFounded SigmaStep.terminating M

theorem SigmaNormalForm.steps {M N : Trm V} (h : SigmaNormalForm M N) :
    SigmaSteps M N :=
  h.1

theorem SigmaNormalForm.normal {M N : Trm V} (h : SigmaNormalForm M N) :
    SigmaNormal N :=
  h.2

theorem SigmaNormalForm.of_steps_normal {M N : Trm V}
    (steps : SigmaSteps M N) (normal : SigmaNormal N) :
    SigmaNormalForm M N :=
  ⟨steps, normal⟩

theorem SigmaNormal.normal_form_self {M : Trm V} (h : SigmaNormal M) :
    SigmaNormalForm M M :=
  ⟨Relation.ReflTransGen.refl, h⟩

@[simp] theorem not_ext_var (x : V) : not_ext (.var x : Trm V) := by
  simp [not_ext]

@[simp] theorem not_ext_lam (x : V) (M : Trm V) : not_ext (.lam x M : Trm V) := by
  simp [not_ext]

@[simp] theorem not_ext_app (M N : Trm V) : not_ext (.app M N : Trm V) := by
  simp [not_ext]

@[simp] theorem not_ext_id : not_ext (.id : Trm V) := by
  simp [not_ext]

@[simp] theorem not_ext_comp (M N : Trm V) : not_ext (.comp M N : Trm V) := by
  simp [not_ext]

@[simp] theorem not_ext_ext (M : Trm V) (x : V) (N : Trm V) : ¬ not_ext (.ext M x N : Trm V) := by
  simp [not_ext]

theorem sigma_normal_TId : SigmaNormal (.id : Trm V) := by
  intro N h
  cases h

theorem sigma_normal_TVar (x : V) : SigmaNormal (.var x : Trm V) := by
  intro N h
  cases h

theorem sigma_normal_lam {x : V} {M : Trm V} (h : SigmaNormal M) :
    SigmaNormal (.lam x M : Trm V) := by
  intro P step
  cases step with
  | lam _ hM => exact h _ hM

theorem sigma_normal_app {M N : Trm V} (hM : SigmaNormal M) (hN : SigmaNormal N) :
    SigmaNormal (.app M N : Trm V) := by
  intro P step
  cases step with
  | appLeft _ h => exact hM _ h
  | appRight _ h => exact hN _ h

theorem sigma_normal_ext {x : V} {M N : Trm V} (hM : SigmaNormal M) (hN : SigmaNormal N) :
    SigmaNormal (.ext M x N : Trm V) := by
  intro P step
  cases step with
  | extLeft _ _ h => exact hM _ h
  | extRight _ _ h => exact hN _ h

theorem sigma_normal_TLam_iff {x : V} {M : Trm V} :
    SigmaNormal (.lam x M : Trm V) ↔ SigmaNormal M := by
  constructor
  · intro h
    intro N step
    exact h _ (SigmaStep.lam x step)
  · intro h
    exact sigma_normal_lam h

theorem sigma_normal_TApp_iff {M N : Trm V} :
    SigmaNormal (.app M N : Trm V) ↔ SigmaNormal M ∧ SigmaNormal N := by
  constructor
  · intro h
    constructor
    · intro P step
      exact h _ (SigmaStep.appLeft N step)
    · intro P step
      exact h _ (SigmaStep.appRight M step)
  · rintro ⟨hM, hN⟩
    exact sigma_normal_app hM hN

theorem sigma_normal_TExt_iff {x : V} {M N : Trm V} :
    SigmaNormal (.ext M x N : Trm V) ↔ SigmaNormal M ∧ SigmaNormal N := by
  constructor
  · intro h
    constructor
    · intro P step
      exact h _ (SigmaStep.extLeft x N step)
    · intro P step
      exact h _ (SigmaStep.extRight M x step)
  · rintro ⟨hM, hN⟩
    exact sigma_normal_ext (x := x) hM hN

theorem sigma_normal_TComp_lam_iff {x : V} {M N : Trm V} :
    SigmaNormal (.comp (.lam x M) N : Trm V) ↔
      SigmaNormal M ∧ SigmaNormal N ∧ N ≠ .id := by
  constructor
  · intro h
    constructor
    · intro P step
      exact h _ (SigmaStep.compLeft N (SigmaStep.lam x step))
    · constructor
      · intro P step
        exact h _ (SigmaStep.compRight (.lam x M) step)
      · intro hEq
        subst hEq
        exact h _ (SigmaStep.idRight (.lam x M))
  · rintro ⟨hM, hN, hNid⟩
    intro P step
    cases step with
    | compLeft _ h =>
        cases h with
        | lam _ hM' => exact hM _ hM'
    | compRight _ h => exact hN _ h
    | idRight _ => exact hNid rfl

theorem sigma_normal_TComp_var_iff {x : V} {W : Trm V} :
    SigmaNormal (.comp (.var x) W : Trm V) ↔
      SigmaNormal W ∧ not_ext W ∧ W ≠ .id := by
  constructor
  · intro h
    have hW : SigmaNormal W := by
      intro P step
      exact h _ (SigmaStep.compRight (.var x) step)
    have hNid : W ≠ .id := by
      intro hEq
      subst hEq
      exact h _ (SigmaStep.idRight (.var x))
    have hNotExt : not_ext W := by
      cases W with
      | ext M y N =>
          by_cases hxy : x = y
          · subst hxy
            exact False.elim (h _ (SigmaStep.varRef x M N))
          · exact False.elim (h _ (SigmaStep.varSkip M y N x (by
              intro hyx
              exact hxy hyx.symm)))
      | _ => simp [not_ext]
    exact ⟨hW, hNotExt, hNid⟩
  · rintro ⟨hW, hNotExt, hNid⟩
    intro P step
    cases step with
    | compLeft _ h => cases h
    | compRight _ h => exact hW _ h
    | idRight _ => exact hNid rfl
    | varRef _ _ _ =>
        cases hNotExt
    | varSkip _ _ _ _ _ =>
        cases hNotExt

def sigma_normal_syntax_corrected (U : Trm V) : Prop :=
  U = .id ∨
    (∃ U1 x U2, U = .ext U1 x U2 ∧ SigmaNormal U1 ∧ SigmaNormal U2) ∨
    (∃ x, U = .var x) ∨
    (∃ U1 U2, U = .app U1 U2 ∧ SigmaNormal U1 ∧ SigmaNormal U2) ∨
    (∃ x U1, U = .lam x U1 ∧ SigmaNormal U1) ∨
    (∃ x U1 U2, U = .comp (.lam x U1) U2 ∧ SigmaNormal U1 ∧ SigmaNormal U2 ∧ U2 ≠ .id) ∨
    (∃ x W, U = .comp (.var x) W ∧ SigmaNormal W ∧ not_ext W ∧ W ≠ .id)

theorem sigma_normal_TComp_cases_for_par_refl {A B : Trm V}
    (h : SigmaNormal (.comp A B : Trm V)) :
    (∃ x M, A = .lam x M ∧ SigmaNormal M ∧ SigmaNormal B ∧ B ≠ .id) ∨
      (∃ x, A = .var x ∧ SigmaNormal B ∧ not_ext B ∧ B ≠ .id) := by
  cases A with
  | var x =>
      right
      have hB : SigmaNormal B ∧ not_ext B ∧ B ≠ .id :=
        (sigma_normal_TComp_var_iff (x := x) (W := B)).mp h
      exact ⟨x, rfl, hB.1, hB.2.1, hB.2.2⟩
  | lam x M =>
      left
      have hB : SigmaNormal M ∧ SigmaNormal B ∧ B ≠ .id :=
        (sigma_normal_TComp_lam_iff (x := x) (M := M) (N := B)).mp h
      exact ⟨x, M, rfl, hB.1, hB.2.1, hB.2.2⟩
  | app M N =>
      exfalso
      exact h _ (SigmaStep.distApp M N B)
  | id =>
      exfalso
      exact h _ (SigmaStep.idLeft B)
  | ext M x N =>
      exfalso
      exact h _ (SigmaStep.distExt M x N B)
  | comp M N =>
      exfalso
      exact h _ (SigmaStep.ass M N B)

theorem sigma_normal_form_lam {x : V} {M M' : Trm V}
    (h : SigmaNormalForm M M') :
    SigmaNormalForm (.lam x M : Trm V) (.lam x M') := by
  exact SigmaNormalForm.of_steps_normal (SigmaSteps.lam x h.steps) (sigma_normal_lam h.normal)

theorem sigma_normal_form_app {M M' N N' : Trm V}
    (hM : SigmaNormalForm M M') (hN : SigmaNormalForm N N') :
    SigmaNormalForm (.app M N : Trm V) (.app M' N') := by
  exact SigmaNormalForm.of_steps_normal
    (SigmaSteps.trans (SigmaSteps.app_left hM.steps) (SigmaSteps.app_right hN.steps))
    (sigma_normal_app hM.normal hN.normal)

theorem sigma_normal_form_ext {x : V} {M M' N N' : Trm V}
    (hM : SigmaNormalForm M M') (hN : SigmaNormalForm N N') :
    SigmaNormalForm (.ext M x N : Trm V) (.ext M' x N') := by
  exact SigmaNormalForm.of_steps_normal
    (SigmaSteps.trans (SigmaSteps.ext_left x hM.steps) (SigmaSteps.ext_right x hN.steps))
    (sigma_normal_ext (x := x) hM.normal hN.normal)

theorem newman {r : α → α → Prop}
    (wf : WellFounded fun N M => r M N) (lc : LocallyConfluent r) :
    Confluent r := by
  intro M
  refine @WellFounded.induction α (fun N M => r M N) wf
    (fun M => ∀ ⦃N L⦄, Relation.ReflTransGen r M N →
      Relation.ReflTransGen r M L → Joinable r N L) M ?_
  intro M ih N L MN ML
  rcases Relation.ReflTransGen.cases_head MN with rfl | ⟨N', MN', N'N⟩
  · exact ⟨L, ML, Relation.ReflTransGen.refl⟩
  · rcases Relation.ReflTransGen.cases_head ML with rfl | ⟨L', ML', L'L⟩
    · exact ⟨N, Relation.ReflTransGen.refl, Relation.ReflTransGen.head MN' N'N⟩
    · rcases lc M N' L' MN' ML' with ⟨P, N'P, L'P⟩
      rcases ih N' MN' N'N N'P with ⟨Q, NQ, PQ⟩
      have L'Q : Relation.ReflTransGen r L' Q := Relation.ReflTransGen.trans L'P PQ
      rcases ih L' ML' L'Q L'L with ⟨R, QR, LR⟩
      exact ⟨R, Relation.ReflTransGen.trans NQ QR, LR⟩

theorem SigmaStep.confluent : Confluent (@SigmaStep V) :=
  newman SigmaStep.terminating SigmaStep.locallyConfluent

theorem NormalFor.eq_of_reflTransGen {r : α → α → Prop} {N P : α}
    (normal : NormalFor r N) (steps : Relation.ReflTransGen r N P) :
    N = P :=
  no_step_reflTransGen_eq steps normal

theorem SigmaNormal.eq_of_steps {N P : Trm V}
    (normal : SigmaNormal N) (steps : SigmaSteps N P) :
    N = P :=
  NormalFor.eq_of_reflTransGen normal steps

theorem SigmaNormalForm.unique {M N₁ N₂ : Trm V}
    (h₁ : SigmaNormalForm M N₁) (h₂ : SigmaNormalForm M N₂) :
    N₁ = N₂ := by
  rcases SigmaStep.confluent h₁.1 h₂.1 with ⟨P, N₁P, N₂P⟩
  have e₁ : N₁ = P := SigmaNormal.eq_of_steps h₁.2 N₁P
  have e₂ : N₂ = P := SigmaNormal.eq_of_steps h₂.2 N₂P
  exact e₁.trans e₂.symm

noncomputable def sigmaNormalize (M : Trm V) : Trm V :=
  Classical.choose (SigmaNormalForm.exists M)

theorem sigmaNormalize_normalForm (M : Trm V) :
    SigmaNormalForm M (sigmaNormalize M) :=
  Classical.choose_spec (SigmaNormalForm.exists M)

theorem sigmaNormalize_steps (M : Trm V) :
    SigmaSteps M (sigmaNormalize M) :=
  (sigmaNormalize_normalForm M).steps

theorem sigmaNormalize_normal (M : Trm V) :
    SigmaNormal (sigmaNormalize M) :=
  (sigmaNormalize_normalForm M).normal

theorem sigmaNormalize_eq_of_normalForm {M N : Trm V}
    (h : SigmaNormalForm M N) :
    sigmaNormalize M = N :=
  SigmaNormalForm.unique (sigmaNormalize_normalForm M) h

theorem sigmaNormalize_eq_of_normal {M : Trm V} (h : SigmaNormal M) :
    sigmaNormalize M = M :=
  sigmaNormalize_eq_of_normalForm (SigmaNormal.normal_form_self h)

theorem SigmaSteps.to_normalForm {M N L : Trm V}
    (steps : SigmaSteps M N) (nf : SigmaNormalForm M L) :
    SigmaSteps N L := by
  rcases SigmaStep.confluent steps nf.steps with ⟨P, NP, LP⟩
  have hLP : L = P := SigmaNormal.eq_of_steps nf.normal LP
  rw [hLP]
  exact NP

theorem sigmaNormalize_eq_of_steps {M N : Trm V} (steps : SigmaSteps M N) :
    sigmaNormalize M = sigmaNormalize N := by
  have nfM : SigmaNormalForm M (sigmaNormalize M) := sigmaNormalize_normalForm M
  have stepsN : SigmaSteps N (sigmaNormalize M) :=
    SigmaSteps.to_normalForm steps nfM
  have nfN : SigmaNormalForm N (sigmaNormalize M) :=
    SigmaNormalForm.of_steps_normal stepsN nfM.normal
  exact (SigmaNormalForm.unique (sigmaNormalize_normalForm N) nfN).symm

theorem sigmaNormalize_eq_of_step {M N : Trm V} (step : SigmaStep M N) :
    sigmaNormalize M = sigmaNormalize N :=
  sigmaNormalize_eq_of_steps (SigmaStep.toSteps step)

theorem sigmaNormalize_comp_right_normalize (A B : Trm V) :
    sigmaNormalize (.comp A (sigmaNormalize B)) = sigmaNormalize (.comp A B) := by
  exact (sigmaNormalize_eq_of_steps (SigmaSteps.comp_right (sigmaNormalize_steps B))).symm

theorem sigmaNormalize_comp_left_normalize (A B : Trm V) :
    sigmaNormalize (.comp (sigmaNormalize A) B) = sigmaNormalize (.comp A B) := by
  exact (sigmaNormalize_eq_of_steps (SigmaSteps.comp_left (sigmaNormalize_steps A))).symm

theorem sigma_normalize_lam {x : V} {M : Trm V} :
    sigmaNormalize (.lam x M : Trm V) = .lam x (sigmaNormalize M) := by
  exact sigmaNormalize_eq_of_normalForm
    (sigma_normal_form_lam (x := x) (M := M) (M' := sigmaNormalize M)
      (sigmaNormalize_normalForm M))

theorem sigma_normalize_app {M N : Trm V} :
    sigmaNormalize (.app M N : Trm V) = .app (sigmaNormalize M) (sigmaNormalize N) := by
  exact sigmaNormalize_eq_of_normalForm
    (sigma_normal_form_app (hM := sigmaNormalize_normalForm M) (hN := sigmaNormalize_normalForm N))

theorem sigma_normalize_ext {x : V} {M N : Trm V} :
    sigmaNormalize (.ext M x N : Trm V) = .ext (sigmaNormalize M) x (sigmaNormalize N) := by
  exact sigmaNormalize_eq_of_normalForm
    (sigma_normal_form_ext (x := x) (hM := sigmaNormalize_normalForm M)
      (hN := sigmaNormalize_normalForm N))

theorem sigma_normalize_comp_id_left {V' : Trm V} (h : SigmaNormal V') :
    sigmaNormalize (.comp .id V' : Trm V) = V' := by
  exact sigmaNormalize_eq_of_normalForm
    ⟨SigmaStep.toSteps (SigmaStep.idLeft V'), h⟩

theorem sigma_normalize_comp_id_right {U : Trm V} (h : SigmaNormal U) :
    sigmaNormalize (.comp U .id : Trm V) = U := by
  exact sigmaNormalize_eq_of_normalForm
    ⟨SigmaStep.toSteps (SigmaStep.idRight U), h⟩

theorem sigma_normalize_comp_lam_id {x : V} {M E : Trm V}
    (h : sigmaNormalize E = .id) :
    sigmaNormalize (.comp (.lam x M) E : Trm V) = .lam x (sigmaNormalize M) := by
  have e_steps : SigmaSteps E .id := by
    simpa [h] using (sigmaNormalize_steps E)
  have m_steps : SigmaSteps M (sigmaNormalize M) := sigmaNormalize_steps M
  have steps1 : SigmaSteps (.comp (.lam x M) E) (.comp (.lam x (sigmaNormalize M)) E) :=
    SigmaSteps.comp_left (SigmaSteps.lam x m_steps)
  have steps2 : SigmaSteps (.comp (.lam x (sigmaNormalize M)) E) (.comp (.lam x (sigmaNormalize M)) .id) :=
    SigmaSteps.comp_right e_steps
  have steps3 : SigmaSteps (.comp (.lam x (sigmaNormalize M)) .id) (.lam x (sigmaNormalize M)) :=
    SigmaStep.toSteps (SigmaStep.idRight (.lam x (sigmaNormalize M)))
  have steps : SigmaSteps (.comp (.lam x M) E) (.lam x (sigmaNormalize M)) :=
    SigmaSteps.trans steps1 (SigmaSteps.trans steps2 steps3)
  have normal : SigmaNormal (.lam x (sigmaNormalize M)) := sigma_normal_lam (sigmaNormalize_normal M)
  exact sigmaNormalize_eq_of_normalForm ⟨steps, normal⟩

theorem sigma_normalize_comp_lam_not_id {x : V} {M E : Trm V}
    (h : sigmaNormalize E ≠ .id) :
    sigmaNormalize (.comp (.lam x M) E : Trm V) =
      .comp (.lam x (sigmaNormalize M)) (sigmaNormalize E) := by
  have m_steps : SigmaSteps M (sigmaNormalize M) := sigmaNormalize_steps M
  have e_steps : SigmaSteps E (sigmaNormalize E) := sigmaNormalize_steps E
  have steps1 : SigmaSteps (.comp (.lam x M) E) (.comp (.lam x (sigmaNormalize M)) E) :=
    SigmaSteps.comp_left (SigmaSteps.lam x m_steps)
  have steps2 : SigmaSteps (.comp (.lam x (sigmaNormalize M)) E)
      (.comp (.lam x (sigmaNormalize M)) (sigmaNormalize E)) :=
    SigmaSteps.comp_right e_steps
  have steps : SigmaSteps (.comp (.lam x M) E)
      (.comp (.lam x (sigmaNormalize M)) (sigmaNormalize E)) :=
    SigmaSteps.trans steps1 steps2
  have normal : SigmaNormal (.comp (.lam x (sigmaNormalize M)) (sigmaNormalize E)) := by
    exact (sigma_normal_TComp_lam_iff (x := x) (M := sigmaNormalize M)
      (N := sigmaNormalize E)).2 ⟨sigmaNormalize_normal M, sigmaNormalize_normal E, h⟩
  exact sigmaNormalize_eq_of_normalForm ⟨steps, normal⟩

theorem sigma_normalize_comp_ext {x : V} {U1 U2 V' : Trm V}
    (nU1 : SigmaNormal U1) (nU2 : SigmaNormal U2) (nV : SigmaNormal V') :
    sigmaNormalize (.comp (.ext U1 x U2) V' : Trm V) =
      .ext (sigmaNormalize (.comp U1 V')) x (sigmaNormalize (.comp U2 V')) := by
  have root : SigmaSteps (.comp (.ext U1 x U2) V')
      (.ext (.comp U1 V') x (.comp U2 V')) :=
    SigmaStep.toSteps (SigmaStep.distExt U1 x U2 V')
  have left_steps : SigmaSteps (.ext (.comp U1 V') x (.comp U2 V'))
      (.ext (sigmaNormalize (.comp U1 V')) x (.comp U2 V')) :=
    SigmaSteps.ext_left x (sigmaNormalize_steps (.comp U1 V'))
  have right_steps : SigmaSteps (.ext (sigmaNormalize (.comp U1 V')) x (.comp U2 V'))
      (.ext (sigmaNormalize (.comp U1 V')) x (sigmaNormalize (.comp U2 V'))) :=
    SigmaSteps.ext_right x (sigmaNormalize_steps (.comp U2 V'))
  have steps : SigmaSteps (.comp (.ext U1 x U2) V')
      (.ext (sigmaNormalize (.comp U1 V')) x (sigmaNormalize (.comp U2 V'))) :=
    SigmaSteps.trans root (SigmaSteps.trans left_steps right_steps)
  have normal : SigmaNormal (.ext (sigmaNormalize (.comp U1 V')) x (sigmaNormalize (.comp U2 V'))) :=
    sigma_normal_ext (x := x) (sigmaNormalize_normal (.comp U1 V')) (sigmaNormalize_normal (.comp U2 V'))
  exact sigmaNormalize_eq_of_normalForm ⟨steps, normal⟩

theorem sigma_normalize_comp_var_ext_same {A B : Trm V} (x : V)
    (nA : SigmaNormal A) (nB : SigmaNormal B) :
    sigmaNormalize (.comp (.var x) (.ext A x B)) = A := by
  calc
    sigmaNormalize (.comp (.var x) (.ext A x B)) = sigmaNormalize A :=
      sigmaNormalize_eq_of_step (SigmaStep.varRef x A B)
    _ = A := sigmaNormalize_eq_of_normal nA

theorem sigma_normalize_comp_var_ext_diff {A B : Trm V} {x y : V}
    (hxy : x ≠ y) (nA : SigmaNormal A) (nB : SigmaNormal B) :
    sigmaNormalize (.comp (.var x) (.ext A y B)) = sigmaNormalize (.comp (.var x) B) := by
  exact sigmaNormalize_eq_of_step (SigmaStep.varSkip A y B x (by
    intro hyx
    exact hxy hyx.symm))

theorem sigma_normalize_comp_app {M N V' : Trm V}
    (nM : SigmaNormal M) (nN : SigmaNormal N) (nV : SigmaNormal V') :
    sigmaNormalize (.comp (.app M N) V') =
      .app (sigmaNormalize (.comp M V')) (sigmaNormalize (.comp N V')) := by
  calc
    sigmaNormalize (.comp (.app M N) V') =
        sigmaNormalize (.app (.comp M V') (.comp N V')) :=
      sigmaNormalize_eq_of_step (SigmaStep.distApp M N V')
    _ = .app (sigmaNormalize (.comp M V')) (sigmaNormalize (.comp N V')) :=
      sigma_normalize_app

theorem sigma_normalize_comp_comp {A B V' : Trm V}
    (nA : SigmaNormal A) (nB : SigmaNormal B) (nV : SigmaNormal V') :
    sigmaNormalize (.comp (.comp A B) V') = sigmaNormalize (.comp A (.comp B V')) :=
  sigmaNormalize_eq_of_step (SigmaStep.ass A B V')

theorem sigma_normalize_comp_lam {x : V} {M V' : Trm V}
    (nM : SigmaNormal M) (nV : SigmaNormal V') (hV : V' ≠ .id) :
    sigmaNormalize (.comp (.lam x M) V') = .comp (.lam x M) V' :=
  sigmaNormalize_eq_of_normal (sigma_normal_TComp_lam_iff.mpr ⟨nM, nV, hV⟩)

theorem sigma_normalize_comp_var_not_ext {x : V} {W : Trm V}
    (nW : SigmaNormal W) (hNotExt : not_ext W) (hW : W ≠ .id) :
    sigmaNormalize (.comp (.var x) W) = .comp (.var x) W :=
  sigmaNormalize_eq_of_normal (sigma_normal_TComp_var_iff.mpr ⟨nW, hNotExt, hW⟩)

theorem sigma_normalize_comp_beta1_target_id {U A : Trm V} {x : V}
    (nU : SigmaNormal U) (nA : SigmaNormal A) :
    sigmaNormalize (.comp (sigmaNormalize (.comp U (.ext A x .id))) .id) =
      sigmaNormalize (.comp U (.ext A x .id)) :=
  sigma_normalize_comp_id_right (sigmaNormalize_normal _)

theorem sigma_normalize_comp_beta1_target_non_id {U A E : Trm V} {x : V}
    (nU : SigmaNormal U) (nA : SigmaNormal A) (nE : SigmaNormal E) (hE : E ≠ .id) :
    sigmaNormalize (.comp (sigmaNormalize (.comp U (.ext A x .id))) E) =
      sigmaNormalize (.comp U (.ext (sigmaNormalize (.comp A E)) x E)) := by
  let K : Trm V := .comp U (.ext A x .id)
  let M : Trm V := .comp K E
  let N : Trm V := .comp (sigmaNormalize K) E
  let R : Trm V := .comp U (.ext (sigmaNormalize (.comp A E)) x E)
  have mN : SigmaSteps M N := by
    exact SigmaSteps.comp_left (sigmaNormalize_steps K)
  have rootAss : SigmaSteps M (.comp U (.comp (.ext A x .id) E)) :=
    SigmaStep.toSteps (SigmaStep.ass U (.ext A x .id) E)
  have rootExt : SigmaSteps (.comp (.ext A x .id) E)
      (.ext (.comp A E) x (.comp .id E)) :=
    SigmaStep.toSteps (SigmaStep.distExt A x .id E)
  have sExt : SigmaSteps (.comp U (.comp (.ext A x .id) E))
      (.comp U (.ext (.comp A E) x (.comp .id E))) :=
    SigmaSteps.comp_right rootExt
  have sA : SigmaSteps (.comp A E) (sigmaNormalize (.comp A E)) := sigmaNormalize_steps _
  have sId : SigmaSteps (.comp .id E) E := SigmaStep.toSteps (SigmaStep.idLeft E)
  have sLeft : SigmaSteps (.ext (.comp A E) x (.comp .id E))
      (.ext (sigmaNormalize (.comp A E)) x (.comp .id E)) :=
    SigmaSteps.ext_left x sA
  have sRight : SigmaSteps (.ext (sigmaNormalize (.comp A E)) x (.comp .id E))
      (.ext (sigmaNormalize (.comp A E)) x E) :=
    SigmaSteps.ext_right x sId
  have mR : SigmaSteps M R :=
    SigmaSteps.trans rootAss (SigmaSteps.trans sExt
      (SigmaSteps.comp_right (SigmaSteps.trans sLeft sRight)))
  have nEq : sigmaNormalize N = sigmaNormalize M := (sigmaNormalize_eq_of_steps mN).symm
  have rEq : sigmaNormalize R = sigmaNormalize M := (sigmaNormalize_eq_of_steps mR).symm
  exact nEq.trans rEq.symm

theorem sigma_normalize_comp_beta2_target {U A W E : Trm V} {x : V}
    (nU : SigmaNormal U) (nA : SigmaNormal A) (nW : SigmaNormal W) (nE : SigmaNormal E) :
    sigmaNormalize (.comp (sigmaNormalize (.comp U (.ext A x W))) E) =
      sigmaNormalize (.comp U (.ext (sigmaNormalize (.comp A E)) x
        (sigmaNormalize (.comp W E)))) := by
  let K : Trm V := .comp U (.ext A x W)
  let M : Trm V := .comp K E
  let N : Trm V := .comp (sigmaNormalize K) E
  let R : Trm V := .comp U (.ext (sigmaNormalize (.comp A E)) x (sigmaNormalize (.comp W E)))
  have mN : SigmaSteps M N := SigmaSteps.comp_left (sigmaNormalize_steps K)
  have rootAss : SigmaSteps M (.comp U (.comp (.ext A x W) E)) :=
    SigmaStep.toSteps (SigmaStep.ass U (.ext A x W) E)
  have rootExt : SigmaSteps (.comp (.ext A x W) E)
      (.ext (.comp A E) x (.comp W E)) :=
    SigmaStep.toSteps (SigmaStep.distExt A x W E)
  have sExt := SigmaSteps.comp_right (L := U) rootExt
  have sA : SigmaSteps (.comp A E) (sigmaNormalize (.comp A E)) := sigmaNormalize_steps _
  have sW : SigmaSteps (.comp W E) (sigmaNormalize (.comp W E)) := sigmaNormalize_steps _
  have sLeft : SigmaSteps (.ext (.comp A E) x (.comp W E))
      (.ext (sigmaNormalize (.comp A E)) x (.comp W E)) :=
    SigmaSteps.ext_left x sA
  have sRight : SigmaSteps (.ext (sigmaNormalize (.comp A E)) x (.comp W E))
      (.ext (sigmaNormalize (.comp A E)) x (sigmaNormalize (.comp W E))) :=
    SigmaSteps.ext_right x sW
  have mR : SigmaSteps M R :=
    SigmaSteps.trans rootAss (SigmaSteps.trans sExt
      (SigmaSteps.comp_right (SigmaSteps.trans sLeft sRight)))
  have nEq : sigmaNormalize N = sigmaNormalize M := (sigmaNormalize_eq_of_steps mN).symm
  have rEq : sigmaNormalize R = sigmaNormalize M := (sigmaNormalize_eq_of_steps mR).symm
  exact nEq.trans rEq.symm

end LambdaEnv
