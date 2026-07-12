import LambdaEnv.BetaModuloSigma

namespace LambdaEnv

theorem weakSteps_lam {M N : Trm α} (x : α) (steps : WeakSteps M N) :
    WeakSteps (.lam x M) (.lam x N) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.lam x step)

theorem weakSteps_app_left {M N L : Trm α} (steps : WeakSteps M N) :
    WeakSteps (.app M L) (.app N L) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.appLeft L step)

theorem weakSteps_app_right {M N L : Trm α} (steps : WeakSteps M N) :
    WeakSteps (.app L M) (.app L N) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.appRight L step)

theorem weakSteps_ext_left {M N L : Trm α} (x : α) (steps : WeakSteps M N) :
    WeakSteps (.ext M x L) (.ext N x L) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.extLeft x L step)

theorem weakSteps_ext_right {M N L : Trm α} (x : α) (steps : WeakSteps M N) :
    WeakSteps (.ext L x M) (.ext L x N) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.extRight L x step)

theorem weakSteps_comp_left {M N L : Trm α} (steps : WeakSteps M N) :
    WeakSteps (.comp M L) (.comp N L) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.compLeft L step)

theorem weakSteps_comp_right {M N L : Trm α} (steps : WeakSteps M N) :
    WeakSteps (.comp L M) (.comp L N) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (WeakStep.compRight L step)

theorem sigmaNormalize_weakSteps (M : Trm α) : WeakSteps M (sigmaNormalize M) :=
  (sigmaNormalize_steps M).toWeakSteps

/-- Isabelle `par_step_subset_weak_steps`. -/
theorem parStep_subset_weakSteps {M N : Trm α} (step : ParStep M N) :
    WeakSteps M N := by
  induction step with
  | var => exact Relation.ReflTransGen.refl
  | lam step ih => exact weakSteps_lam _ ih
  | app hM hN ihM ihN =>
      exact Relation.ReflTransGen.trans (weakSteps_app_left ihM) (weakSteps_app_right ihN)
  | id => exact Relation.ReflTransGen.refl
  | ext hM hN ihM ihN =>
      exact Relation.ReflTransGen.trans (weakSteps_ext_left _ ihM) (weakSteps_ext_right _ ihN)
  | lamComp hU hW hWne hW'ne ihU ihW =>
      exact Relation.ReflTransGen.trans
        (weakSteps_comp_left (weakSteps_lam _ ihU)) (weakSteps_comp_right ihW)
  | lamCompId hU hW hWne ihU ihW =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.trans
          (weakSteps_comp_left (weakSteps_lam _ ihU)) (weakSteps_comp_right ihW))
        (Relation.ReflTransGen.single (WeakStep.idRight _))
  | varComp hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact weakSteps_comp_right ihW
  | varCompOther hW hNotExt hNotExt' hWne hW'ne ihW =>
      exact Relation.ReflTransGen.trans (weakSteps_comp_right ihW)
        (sigmaNormalize_weakSteps _)
  | varCompId hW hNotExt hWne ihW =>
      exact Relation.ReflTransGen.trans (weakSteps_comp_right ihW)
        (Relation.ReflTransGen.single (WeakStep.idRight _))
  | beta1 hU hA ihU ihA =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.trans
          (weakSteps_app_left (weakSteps_lam _ ihU)) (weakSteps_app_right ihA))
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (WeakStep.beta2 _ _ _)) (sigmaNormalize_weakSteps _))
  | beta2 hWne hU hA hW ihU ihA ihW =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.trans
            (weakSteps_app_left (weakSteps_comp_left (weakSteps_lam _ ihU)))
            (weakSteps_app_left (weakSteps_comp_right ihW)))
          (weakSteps_app_right ihA))
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (WeakStep.beta1 _ _ _ _)) (sigmaNormalize_weakSteps _))

/-- Isabelle `beta_mod_sigma_rel_subset_weak_steps`. -/
theorem betaModSigmaRel_subset_weakSteps {M N : Trm α} (h : BetaModSigmaRel M N) :
    WeakSteps M N :=
  parStep_subset_weakSteps (betaModSigmaRel_imp_parStep h)

/-- Isabelle `weak_step_lift_to_beta_mod_sigma`. -/
theorem weakStep_lift_to_betaModSigma {M N : Trm α} (step : WeakStep M N) :
    BetaModSigmaSteps (sigmaNormalize M) (sigmaNormalize N) := by
  rcases step.sigma_or_beta with sigma | beta
  · have eq : sigmaNormalize N = sigmaNormalize M :=
      (sigmaNormalize_eq_of_step sigma).symm
    rw [eq]
  · exact parStep_subset_betaModSigmaSteps (betaStep_to_parStep_normalized beta)

theorem reflTransGen_lift_by_steps {p q : α → α → Prop}
    (lift : ∀ ⦃x y⦄, p x y → Relation.ReflTransGen q x y)
    {x y : α} (steps : Relation.ReflTransGen p x y) : Relation.ReflTransGen q x y := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.trans ih (lift step)

theorem reflTransGen_lift_by_normalization {r rp : α → α → Prop} (nf : α → α)
    (lift : ∀ ⦃x y⦄, r x y → Relation.ReflTransGen rp (nf x) (nf y))
    {x y : α} (steps : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen rp (nf x) (nf y) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.trans ih (lift step)

/-- Hardin's forward-confluence lemma, as used in Isabelle's Theorem 3.16. -/
theorem hardin_forward_confluence {r rp : α → α → Prop} {nf : α → α}
    (nf_reduces : ∀ x, Relation.ReflTransGen r x (nf x))
    (lift_step : ∀ ⦃x y⦄, r x y → Relation.ReflTransGen rp (nf x) (nf y))
    (rp_sub_rstar : ∀ ⦃x y⦄, rp x y → Relation.ReflTransGen r x y)
    (rp_conf : Confluent rp) : Confluent r := by
  intro M N L hMN hML
  have nMN := reflTransGen_lift_by_normalization nf lift_step hMN
  have nML := reflTransGen_lift_by_normalization nf lift_step hML
  rcases rp_conf nMN nML with ⟨Q, hNQ, hLQ⟩
  have rNQ := reflTransGen_lift_by_steps rp_sub_rstar hNQ
  have rLQ := reflTransGen_lift_by_steps rp_sub_rstar hLQ
  exact ⟨Q, Relation.ReflTransGen.trans (nf_reduces N) rNQ,
    Relation.ReflTransGen.trans (nf_reduces L) rLQ⟩

/-- Isabelle `beta_mod_sigma_confluent_imp_weak_step_confluent`. -/
theorem betaModSigma_confluent_imp_weakStep_confluent
    (h : Confluent (@BetaModSigmaRel α)) : Confluent (@WeakStep α) := by
  apply hardin_forward_confluence (nf := sigmaNormalize)
  · exact sigmaNormalize_weakSteps
  · intro M N step
    exact weakStep_lift_to_betaModSigma step
  · intro M N step
    exact betaModSigmaRel_subset_weakSteps step
  · exact h

/-- Isabelle `theorem_3_16_weak_step_confluent`. -/
theorem theorem_3_16_weakStep_confluent : Confluent (@WeakStep α) :=
  betaModSigma_confluent_imp_weakStep_confluent BetaModSigmaRel.confluent

/-- Isabelle `weak_step_confluent`. -/
theorem weakStep_confluent : Confluent (@WeakStep α) :=
  theorem_3_16_weakStep_confluent

end LambdaEnv
