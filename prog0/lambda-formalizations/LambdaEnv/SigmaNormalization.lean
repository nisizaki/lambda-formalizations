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

end LambdaEnv
