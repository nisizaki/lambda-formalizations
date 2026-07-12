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

end LambdaEnv
