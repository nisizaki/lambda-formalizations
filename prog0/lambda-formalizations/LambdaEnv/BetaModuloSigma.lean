import LambdaEnv.ParallelReduction

namespace LambdaEnv

/-- Isabelle `beta_mod_sigma_rel`: one beta step viewed between the unique
sigma normal forms of its endpoints. -/
def BetaModSigmaRel (U V : Trm α) : Prop :=
  SigmaNormal U ∧ SigmaNormal V ∧
    ∃ M N, SigmaNormalForm M U ∧ BetaStep M N ∧ SigmaNormalForm N V

abbrev BetaModSigmaSteps : Trm α → Trm α → Prop :=
  Relation.ReflTransGen BetaModSigmaRel

abbrev ParSteps : Trm α → Trm α → Prop :=
  Relation.ReflTransGen ParStep

theorem BetaModSigmaRel.intro {U N V : Trm α}
    (normalU : SigmaNormal U) (beta : BetaStep U N) (normalForm : SigmaNormalForm N V) :
    BetaModSigmaRel U V :=
  ⟨normalU, normalForm.normal, U, N, normalU.normal_form_self, beta, normalForm⟩

theorem BetaModSigmaRel.elim {U V : Trm α} (h : BetaModSigmaRel U V) :
    ∃ M N, SigmaNormalForm M U ∧ BetaStep M N ∧ SigmaNormalForm N V :=
  h.2.2

theorem betaModSigmaStep {U N : Trm α}
    (normalU : SigmaNormal U) (beta : BetaStep U N) :
    BetaModSigmaSteps U (sigmaNormalize N) := by
  exact Relation.ReflTransGen.single
    (BetaModSigmaRel.intro normalU beta (sigmaNormalize_normalForm N))

end LambdaEnv
