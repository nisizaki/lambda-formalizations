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

/-- Isabelle `beta_step_to_par_step_normalized`. -/
theorem betaStep_to_parStep_normalized {M N : Trm α} (beta : BetaStep M N) :
    ParStep (sigmaNormalize M) (sigmaNormalize N) := by
  induction beta with
  | beta2 x M N =>
      have sExt : SigmaSteps (.ext N x .id) (.ext (sigmaNormalize N) x .id) :=
        SigmaSteps.ext_left x (sigmaNormalize_steps N)
      have sTarget : SigmaSteps (.comp M (.ext N x .id))
          (.comp (sigmaNormalize M) (.ext (sigmaNormalize N) x .id)) :=
        SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps M))
          (SigmaSteps.comp_right sExt)
      have targetEq := sigmaNormalize_eq_of_steps sTarget
      rw [sigma_normalize_app, sigma_normalize_lam, targetEq]
      exact ParStep.beta1 (ParStep.refl (sigmaNormalize_normal M))
        (ParStep.refl (sigmaNormalize_normal N))
  | beta1 x M E L =>
      by_cases hE : sigmaNormalize E = .id
      · have sL : SigmaSteps L (sigmaNormalize L) := sigmaNormalize_steps L
        have sE : SigmaSteps E .id := by
          rw [← hE]
          exact sigmaNormalize_steps E
        have sExt : SigmaSteps (.ext L x E) (.ext (sigmaNormalize L) x .id) :=
          SigmaSteps.trans (SigmaSteps.ext_left x sL) (SigmaSteps.ext_right x sE)
        have sTarget : SigmaSteps (.comp M (.ext L x E))
            (.comp (sigmaNormalize M) (.ext (sigmaNormalize L) x .id)) :=
          SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps M))
            (SigmaSteps.comp_right sExt)
        have targetEq := sigmaNormalize_eq_of_steps sTarget
        rw [sigma_normalize_app, sigma_normalize_comp_lam_id hE, targetEq]
        exact ParStep.beta1 (ParStep.refl (sigmaNormalize_normal M))
          (ParStep.refl (sigmaNormalize_normal L))
      · have sL : SigmaSteps L (sigmaNormalize L) := sigmaNormalize_steps L
        have sExt : SigmaSteps (.ext L x E)
            (.ext (sigmaNormalize L) x (sigmaNormalize E)) :=
          SigmaSteps.trans (SigmaSteps.ext_left x sL)
            (SigmaSteps.ext_right x (sigmaNormalize_steps E))
        have sTarget : SigmaSteps (.comp M (.ext L x E))
            (.comp (sigmaNormalize M)
              (.ext (sigmaNormalize L) x (sigmaNormalize E))) :=
          SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps M))
            (SigmaSteps.comp_right sExt)
        have targetEq := sigmaNormalize_eq_of_steps sTarget
        rw [sigma_normalize_app, sigma_normalize_comp_lam_not_id hE, targetEq]
        exact ParStep.beta2 hE (ParStep.refl (sigmaNormalize_normal M))
          (ParStep.refl (sigmaNormalize_normal L))
          (ParStep.refl (sigmaNormalize_normal E))
  | appLeft L beta ih =>
      rw [sigma_normalize_app, sigma_normalize_app]
      exact ParStep.app ih (ParStep.refl (sigmaNormalize_normal L))
  | appRight L beta ih =>
      rw [sigma_normalize_app, sigma_normalize_app]
      exact ParStep.app (ParStep.refl (sigmaNormalize_normal L)) ih
  | lam x beta ih =>
      rw [sigma_normalize_lam, sigma_normalize_lam]
      exact ParStep.lam ih
  | @compLeft M N L beta ih =>
      have lhs : sigmaNormalize (.comp M L) =
          sigmaNormalize (.comp (sigmaNormalize M) (sigmaNormalize L)) := by
        exact sigmaNormalize_eq_of_steps
          (SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps M))
            (SigmaSteps.comp_right (sigmaNormalize_steps L)))
      have rhs : sigmaNormalize (.comp N L) =
          sigmaNormalize (.comp (sigmaNormalize N) (sigmaNormalize L)) := by
        exact sigmaNormalize_eq_of_steps
          (SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps N))
            (SigmaSteps.comp_right (sigmaNormalize_steps L)))
      rw [lhs, rhs]
      exact ParStep.sigma_comp ih (ParStep.refl (sigmaNormalize_normal L))
  | @compRight M N L beta ih =>
      have lhs : sigmaNormalize (.comp L M) =
          sigmaNormalize (.comp (sigmaNormalize L) (sigmaNormalize M)) := by
        exact sigmaNormalize_eq_of_steps
          (SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps L))
            (SigmaSteps.comp_right (sigmaNormalize_steps M)))
      have rhs : sigmaNormalize (.comp L N) =
          sigmaNormalize (.comp (sigmaNormalize L) (sigmaNormalize N)) := by
        exact sigmaNormalize_eq_of_steps
          (SigmaSteps.trans (SigmaSteps.comp_left (sigmaNormalize_steps L))
            (SigmaSteps.comp_right (sigmaNormalize_steps N)))
      rw [lhs, rhs]
      exact ParStep.sigma_comp (ParStep.refl (sigmaNormalize_normal L)) ih
  | extLeft x L beta ih =>
      rw [sigma_normalize_ext, sigma_normalize_ext]
      exact ParStep.ext ih (ParStep.refl (sigmaNormalize_normal L))
  | extRight L x beta ih =>
      rw [sigma_normalize_ext, sigma_normalize_ext]
      exact ParStep.ext (ParStep.refl (sigmaNormalize_normal L)) ih

theorem betaModSigmaRel_imp_parStep {U V : Trm α} (h : BetaModSigmaRel U V) :
    ParStep U V := by
  rcases h.elim with ⟨M, N, normalFormM, beta, normalFormN⟩
  have sourceEq : sigmaNormalize M = U := sigmaNormalize_eq_of_normalForm normalFormM
  have targetEq : sigmaNormalize N = V := sigmaNormalize_eq_of_normalForm normalFormN
  rw [← sourceEq, ← targetEq]
  exact betaStep_to_parStep_normalized beta

theorem betaModSigmaSteps_subset_parSteps {M N : Trm α}
    (steps : BetaModSigmaSteps M N) : ParSteps M N := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih =>
      exact Relation.ReflTransGen.tail ih (betaModSigmaRel_imp_parStep step)

theorem betaModSigmaRel_lam {U V : Trm α} {x : α}
    (h : BetaModSigmaRel U V) : BetaModSigmaRel (.lam x U) (.lam x V) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  exact ⟨sigma_normal_lam h.1, sigma_normal_lam h.2.1, .lam x M, .lam x N,
    sigma_normal_form_lam nfM, BetaStep.lam x beta, sigma_normal_form_lam nfN⟩

theorem betaModSigmaRel_app_left {U V L : Trm α}
    (h : BetaModSigmaRel U V) (normalL : SigmaNormal L) :
    BetaModSigmaRel (.app U L) (.app V L) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  exact ⟨sigma_normal_app h.1 normalL, sigma_normal_app h.2.1 normalL,
    .app M L, .app N L,
    sigma_normal_form_app nfM normalL.normal_form_self,
    BetaStep.appLeft L beta,
    sigma_normal_form_app nfN normalL.normal_form_self⟩

theorem betaModSigmaRel_app_right {U V L : Trm α}
    (h : BetaModSigmaRel U V) (normalL : SigmaNormal L) :
    BetaModSigmaRel (.app L U) (.app L V) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  exact ⟨sigma_normal_app normalL h.1, sigma_normal_app normalL h.2.1,
    .app L M, .app L N,
    sigma_normal_form_app normalL.normal_form_self nfM,
    BetaStep.appRight L beta,
    sigma_normal_form_app normalL.normal_form_self nfN⟩

theorem betaModSigmaRel_ext_left {U V L : Trm α} {x : α}
    (h : BetaModSigmaRel U V) (normalL : SigmaNormal L) :
    BetaModSigmaRel (.ext U x L) (.ext V x L) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  exact ⟨sigma_normal_ext h.1 normalL, sigma_normal_ext h.2.1 normalL,
    .ext M x L, .ext N x L,
    sigma_normal_form_ext nfM normalL.normal_form_self,
    BetaStep.extLeft x L beta,
    sigma_normal_form_ext nfN normalL.normal_form_self⟩

theorem betaModSigmaRel_ext_right {U V L : Trm α} {x : α}
    (h : BetaModSigmaRel U V) (normalL : SigmaNormal L) :
    BetaModSigmaRel (.ext L x U) (.ext L x V) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  exact ⟨sigma_normal_ext normalL h.1, sigma_normal_ext normalL h.2.1,
    .ext L x M, .ext L x N,
    sigma_normal_form_ext normalL.normal_form_self nfM,
    BetaStep.extRight L x beta,
    sigma_normal_form_ext normalL.normal_form_self nfN⟩

theorem betaModSigmaRel_comp_left_normalize {U V L : Trm α}
    (h : BetaModSigmaRel U V) :
    BetaModSigmaRel (sigmaNormalize (.comp U L)) (sigmaNormalize (.comp V L)) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  have sourceSteps : SigmaSteps (.comp M L) (sigmaNormalize (.comp U L)) :=
    SigmaSteps.trans (SigmaSteps.comp_left nfM.steps) (sigmaNormalize_steps _)
  have targetSteps : SigmaSteps (.comp N L) (sigmaNormalize (.comp V L)) :=
    SigmaSteps.trans (SigmaSteps.comp_left nfN.steps) (sigmaNormalize_steps _)
  exact ⟨sigmaNormalize_normal _, sigmaNormalize_normal _, .comp M L, .comp N L,
    SigmaNormalForm.of_steps_normal sourceSteps (sigmaNormalize_normal _),
    BetaStep.compLeft L beta,
    SigmaNormalForm.of_steps_normal targetSteps (sigmaNormalize_normal _)⟩

theorem betaModSigmaRel_comp_right_normalize {U V L : Trm α}
    (h : BetaModSigmaRel U V) :
    BetaModSigmaRel (sigmaNormalize (.comp L U)) (sigmaNormalize (.comp L V)) := by
  rcases h.elim with ⟨M, N, nfM, beta, nfN⟩
  have sourceSteps : SigmaSteps (.comp L M) (sigmaNormalize (.comp L U)) :=
    SigmaSteps.trans (SigmaSteps.comp_right nfM.steps) (sigmaNormalize_steps _)
  have targetSteps : SigmaSteps (.comp L N) (sigmaNormalize (.comp L V)) :=
    SigmaSteps.trans (SigmaSteps.comp_right nfN.steps) (sigmaNormalize_steps _)
  exact ⟨sigmaNormalize_normal _, sigmaNormalize_normal _, .comp L M, .comp L N,
    SigmaNormalForm.of_steps_normal sourceSteps (sigmaNormalize_normal _),
    BetaStep.compRight L beta,
    SigmaNormalForm.of_steps_normal targetSteps (sigmaNormalize_normal _)⟩

theorem betaModSigmaSteps_lam {U V : Trm α} {x : α}
    (steps : BetaModSigmaSteps U V) : BetaModSigmaSteps (.lam x U) (.lam x V) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (betaModSigmaRel_lam step)

theorem betaModSigmaSteps_app_left {U V L : Trm α}
    (steps : BetaModSigmaSteps U V) (normalL : SigmaNormal L) :
    BetaModSigmaSteps (.app U L) (.app V L) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (betaModSigmaRel_app_left step normalL)

theorem betaModSigmaSteps_app_right {U V L : Trm α}
    (steps : BetaModSigmaSteps U V) (normalL : SigmaNormal L) :
    BetaModSigmaSteps (.app L U) (.app L V) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (betaModSigmaRel_app_right step normalL)

theorem betaModSigmaSteps_ext_left {U V L : Trm α} {x : α}
    (steps : BetaModSigmaSteps U V) (normalL : SigmaNormal L) :
    BetaModSigmaSteps (.ext U x L) (.ext V x L) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (betaModSigmaRel_ext_left step normalL)

theorem betaModSigmaSteps_ext_right {U V L : Trm α} {x : α}
    (steps : BetaModSigmaSteps U V) (normalL : SigmaNormal L) :
    BetaModSigmaSteps (.ext L x U) (.ext L x V) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih => exact Relation.ReflTransGen.tail ih (betaModSigmaRel_ext_right step normalL)

theorem betaModSigmaSteps_comp_left_normalize {U V L : Trm α}
    (steps : BetaModSigmaSteps U V) :
    BetaModSigmaSteps (sigmaNormalize (.comp U L)) (sigmaNormalize (.comp V L)) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih =>
      exact Relation.ReflTransGen.tail ih (betaModSigmaRel_comp_left_normalize step)

theorem betaModSigmaSteps_comp_right_normalize {U V L : Trm α}
    (steps : BetaModSigmaSteps U V) :
    BetaModSigmaSteps (sigmaNormalize (.comp L U)) (sigmaNormalize (.comp L V)) := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih =>
      exact Relation.ReflTransGen.tail ih (betaModSigmaRel_comp_right_normalize step)

theorem parStep_subset_betaModSigmaSteps {M N : Trm α} (step : ParStep M N) :
    BetaModSigmaSteps M N := by
  induction step with
  | var x => exact Relation.ReflTransGen.refl
  | lam h ih => exact betaModSigmaSteps_lam ih
  | app hA hB ihA ihB =>
      have s₁ := betaModSigmaSteps_app_left ihA hB.source_normal
      have s₂ := betaModSigmaSteps_app_right ihB hA.target_normal
      exact Relation.ReflTransGen.trans s₁ s₂
  | id => exact Relation.ReflTransGen.refl
  | @ext U U' V V' x hA hB ihA ihB =>
      have s₁ := betaModSigmaSteps_ext_left (x := x) ihA hB.source_normal
      have s₂ := betaModSigmaSteps_ext_right (x := x) ihB hA.target_normal
      exact Relation.ReflTransGen.trans s₁ s₂
  | @lamComp U U' W W' x hU hW hWne hW'ne ihU ihW =>
      have nSrc : SigmaNormal (.comp (.lam x U) W) :=
        sigma_normal_TComp_lam_iff.mpr ⟨hU.source_normal, hW.source_normal, hWne⟩
      have nTgt : SigmaNormal (.comp (.lam x U') W') :=
        sigma_normal_TComp_lam_iff.mpr ⟨hU.target_normal, hW.target_normal, hW'ne⟩
      have s₁ := betaModSigmaSteps_comp_left_normalize (L := W)
        (betaModSigmaSteps_lam (x := x) ihU)
      have s₂ := betaModSigmaSteps_comp_right_normalize (L := .lam x U') ihW
      have s := Relation.ReflTransGen.trans s₁ s₂
      rw [sigmaNormalize_eq_of_normal nSrc, sigmaNormalize_eq_of_normal nTgt] at s
      exact s
  | @lamCompId U U' W x hU hW hWne ihU ihW =>
      have nSrc : SigmaNormal (.comp (.lam x U) W) :=
        sigma_normal_TComp_lam_iff.mpr ⟨hU.source_normal, hW.source_normal, hWne⟩
      have s₁ := betaModSigmaSteps_comp_left_normalize (L := W)
        (betaModSigmaSteps_lam (x := x) ihU)
      have s₂ := betaModSigmaSteps_comp_right_normalize (L := .lam x U') ihW
      have s := Relation.ReflTransGen.trans s₁ s₂
      have rhs : sigmaNormalize (.comp (.lam x U') .id) = .lam x U' :=
        sigma_normalize_comp_id_right (sigma_normal_lam hU.target_normal)
      rw [sigmaNormalize_eq_of_normal nSrc, rhs] at s
      exact s
  | @varComp W W' x hW hNotExt hNotExt' hWne hW'ne ihW =>
      have nSrc : SigmaNormal (.comp (.var x) W) :=
        sigma_normal_TComp_var_iff.mpr ⟨hW.source_normal, hNotExt, hWne⟩
      have nTgt : SigmaNormal (.comp (.var x) W') :=
        sigma_normal_TComp_var_iff.mpr ⟨hW.target_normal, hNotExt', hW'ne⟩
      have s := betaModSigmaSteps_comp_right_normalize (L := .var x) ihW
      rw [sigmaNormalize_eq_of_normal nSrc, sigmaNormalize_eq_of_normal nTgt] at s
      exact s
  | @varCompOther W W' x hW hNotExt hNotExt' hWne hW'ne ihW =>
      have nSrc : SigmaNormal (.comp (.var x) W) :=
        sigma_normal_TComp_var_iff.mpr ⟨hW.source_normal, hNotExt, hWne⟩
      have s := betaModSigmaSteps_comp_right_normalize (L := .var x) ihW
      rw [sigmaNormalize_eq_of_normal nSrc] at s
      exact s
  | @varCompId W x hW hNotExt hWne ihW =>
      have nSrc : SigmaNormal (.comp (.var x) W) :=
        sigma_normal_TComp_var_iff.mpr ⟨hW.source_normal, hNotExt, hWne⟩
      have s := betaModSigmaSteps_comp_right_normalize (L := .var x) ihW
      have rhs : sigmaNormalize (.comp (.var x) .id) = .var x :=
        sigma_normalize_comp_id_right (sigma_normal_TVar x)
      rw [sigmaNormalize_eq_of_normal nSrc, rhs] at s
      exact s
  | @beta1 U U' A A' x hU hA ihU ihA =>
      have sLam := betaModSigmaSteps_lam (x := x) ihU
      have s₁ := betaModSigmaSteps_app_left sLam hA.source_normal
      have s₂ := betaModSigmaSteps_app_right (L := .lam x U') ihA
        (sigma_normal_lam (x := x) hU.target_normal)
      have appSteps := Relation.ReflTransGen.trans s₁ s₂
      have normalRoot : SigmaNormal (.app (.lam x U') A') :=
        sigma_normal_app (sigma_normal_lam hU.target_normal) hA.target_normal
      have root := betaModSigmaStep normalRoot (BetaStep.beta2 x U' A')
      exact Relation.ReflTransGen.trans appSteps root
  | @beta2 W U U' A A' W' x hWne hU hA hW ihU ihA ihW =>
      have nFun : SigmaNormal (.comp (.lam x U) W) :=
        sigma_normal_TComp_lam_iff.mpr ⟨hU.source_normal, hW.source_normal, hWne⟩
      have sFun₁ := betaModSigmaSteps_comp_left_normalize (L := W)
        (betaModSigmaSteps_lam (x := x) ihU)
      have sFun₂ := betaModSigmaSteps_comp_right_normalize (L := .lam x U') ihW
      have sFun := Relation.ReflTransGen.trans sFun₁ sFun₂
      rw [sigmaNormalize_eq_of_normal nFun] at sFun
      have sApp₁ := betaModSigmaSteps_app_left sFun hA.source_normal
      have nFun' : SigmaNormal (sigmaNormalize (.comp (.lam x U') W')) :=
        sigmaNormalize_normal _
      have sApp₂ := betaModSigmaSteps_app_right (L := sigmaNormalize (.comp (.lam x U') W'))
        ihA nFun'
      have appSteps := Relation.ReflTransGen.trans sApp₁ sApp₂
      by_cases hW'id : W' = .id
      · subst W'
        have funEq : sigmaNormalize (.comp (.lam x U') .id) = .lam x U' :=
          sigma_normalize_comp_id_right (sigma_normal_lam hU.target_normal)
        have normalRoot : SigmaNormal (.app (.lam x U') A') :=
          sigma_normal_app (sigma_normal_lam hU.target_normal) hA.target_normal
        have root := betaModSigmaStep normalRoot (BetaStep.beta2 x U' A')
        rw [funEq] at appSteps
        exact Relation.ReflTransGen.trans appSteps root
      · have hSigmaW' : sigmaNormalize W' = W' :=
          sigmaNormalize_eq_of_normal hW.target_normal
        have hSigmaW'ne : sigmaNormalize W' ≠ .id := by
          rw [hSigmaW']
          exact hW'id
        have funEq : sigmaNormalize (.comp (.lam x U') W') = .comp (.lam x U') W' := by
          rw [sigma_normalize_comp_lam_not_id hSigmaW'ne,
            sigmaNormalize_eq_of_normal hU.target_normal, hSigmaW']
        have normalFun : SigmaNormal (.comp (.lam x U') W') :=
          sigma_normal_TComp_lam_iff.mpr ⟨hU.target_normal, hW.target_normal, hW'id⟩
        have normalRoot : SigmaNormal (.app (.comp (.lam x U') W') A') :=
          sigma_normal_app normalFun hA.target_normal
        have root := betaModSigmaStep normalRoot (BetaStep.beta1 x U' W' A')
        rw [funEq] at appSteps
        exact Relation.ReflTransGen.trans appSteps root

theorem parSteps_subset_betaModSigmaSteps {M N : Trm α}
    (steps : ParSteps M N) : BetaModSigmaSteps M N := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail steps step ih =>
      exact Relation.ReflTransGen.trans ih (parStep_subset_betaModSigmaSteps step)

theorem stronglyConfluent_strip {r : α → α → Prop} (diamond : StronglyConfluent r)
    {a b c : α} (step : r a b) (steps : Relation.ReflTransGen r a c) :
    ∃ d, Relation.ReflTransGen r b d ∧ r c d := by
  induction steps generalizing b with
  | refl => exact ⟨b, Relation.ReflTransGen.refl, step⟩
  | tail steps stepYZ ih =>
      rcases ih step with ⟨e, be, ye⟩
      rcases diamond ye stepYZ with ⟨d, ed, zd⟩
      exact ⟨d, Relation.ReflTransGen.tail be ed, zd⟩

theorem stronglyConfluent_implies_confluent {r : α → α → Prop}
    (diamond : StronglyConfluent r) : Confluent r := by
  intro a b c ab ac
  induction ac generalizing b with
  | refl => exact ⟨b, Relation.ReflTransGen.refl, ab⟩
  | tail ac stepYZ ih =>
      rcases ih ab with ⟨d, bd, yd⟩
      rcases stronglyConfluent_strip diamond stepYZ yd with ⟨e, ze, de⟩
      exact ⟨e, Relation.ReflTransGen.tail bd de, ze⟩

theorem ParStep.confluent : Confluent (@ParStep α) :=
  stronglyConfluent_implies_confluent ParStep.stronglyConfluent

theorem BetaModSigmaRel.confluent : Confluent (@BetaModSigmaRel α) := by
  intro M N L hMN hML
  rcases ParStep.confluent (betaModSigmaSteps_subset_parSteps hMN)
    (betaModSigmaSteps_subset_parSteps hML) with ⟨Q, hNQ, hLQ⟩
  exact ⟨Q, parSteps_subset_betaModSigmaSteps hNQ,
    parSteps_subset_betaModSigmaSteps hLQ⟩

theorem betaModSigma_confluent : Confluent (@BetaModSigmaRel α) :=
  BetaModSigmaRel.confluent

end LambdaEnv
