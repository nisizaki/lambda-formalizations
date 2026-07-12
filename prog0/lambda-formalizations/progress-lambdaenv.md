# LambdaEnv Lean 4 Port Progress

## Current goal

Port `IsabelleSources/LambdaEnv.thy` to Lean 4 in dependency order.  The current
completed slices are `section "Raw terms and length"`, most basic material from
`section "Reduction relations"`, and the first sigma normal-form definitions.

## Isabelle source structure

### Definitions

- `datatype 'v trm`: `TVar`, `TLam`, `TApp`, `TId`, `TExt`, `TComp`
- `fun term_length`
- `definition terminating`
- `definition sigma_steps`
- `definition beta_steps`
- `definition weak_steps`
- `definition joinablep`
- `definition confluentp`
- `definition normal_form_for`
- `definition sigma_normal`
- `definition sigma_normal_form`
- `definition sigma_normalize`
- `definition not_ext`
- `definition sigma_normal_syntax_corrected`
- `fun term_star`
- `definition beta_mod_sigma_rel`
- `definition beta_mod_sigma_fun`
- `abbreviation hardin_R`, `hardin_R1`, `hardin_R2`, `hardin_Rprime`

### Inductive relations

- `sigma_step`: sigma root rules plus contextual closure.
- `sigma_root_step`: sigma root rules only.
- `beta_step`: beta root rules plus contextual closure.
- `weak_step`: union of sigma and beta root rules plus contextual closure.
- `par_step`: parallel reduction over sigma-normal terms.

### Main lemmas

- Length and termination support: `term_length_pos`,
  `term_length_right_less_TComp`, `add_mult_right_less_mono`,
  `add_mult_left_less_mono`, `term_length_comp_sub_*`,
  `sigma_step_decreases_length`.
- Sigma closure and local peaks: `sigma_steps_*`, `sigma_join_*`,
  `sigma_peak_*`, `sigma_step_local_peak_*`,
  `sigma_step_local_peak_joinable`.
- Abstract relation support: `locally_confluentpD`,
  `terminating_imp_wfP_conversep`, `locally_confluentp_to_newman`,
  `newman_lemma`.
- Normal forms: `no_step_rtranclp_eq`, `unique_normal_form`,
  `sigma_normal_form_exists`, `sigma_normal_form_unique`,
  `sigma_nf_*`, `sigma_normal_*`,
  `lemma_3_7_sigma_normal_syntactic_characterization`.
- Star and parallel reduction: `term_star_*`,
  `lemma_3_12_1_term_star_sigma_normal`,
  `lemma_3_9_par_step_sigma_normal`,
  `lemma_3_10_par_step_refl`, `lemma_3_11_*`,
  `lemma_3_13_par_step_to_star`,
  `par_step_strongly_confluent_star`.
- Beta modulo sigma and Hardin interpretation: `beta_mod_sigma_*`,
  `lemma_3_14_*`, `strong_confluence_*`, `par_step_confluent`,
  `lemma_3_15_beta_mod_sigma_confluent`,
  `sigma_normalize_weak_steps`, `hardin_forward_confluence`.

### Main theorems

- `sigma_step_terminating`
- `sigma_step_locally_confluent_if_local_peaks_joinable`
- `sigma_step_locally_confluent`
- `newman_lemma`
- `sigma_step_confluent`
- `lemma_3_7_sigma_normal_syntactic_characterization`
- `lemma_3_12_1_term_star_sigma_normal`
- `par_step_source_sigma_normal`
- `par_step_target_sigma_normal`
- `lemma_3_9_par_step_sigma_normal`
- `lemma_3_10_par_step_refl`
- `lemma_3_11_par_step_sigma_comp`
- `lemma_3_13_par_step_to_star`
- `lemma_3_13_par_step_to_star_normalized`
- `par_step_strongly_confluent_star`
- `lemma_3_14_beta_mod_sigma_subset_par`
- `lemma_3_14_par_subset_beta_mod_sigma_star`
- `lemma_3_14_beta_mod_sigma_par_equiv`
- `beta_step_compatible_with_sigma_normalization_rel`
- `beta_step_compatible_with_sigma_normalization`
- `par_step_confluent`
- `lemma_3_15_beta_mod_sigma_confluent`
- `beta_mod_sigma_confluent`
- `theorem_3_16_weak_step_confluent`
- `weak_step_confluent`

### Isabelle-specific library features

- `rtranclp` will correspond to `Relation.ReflTransGen`.
- `wf`, `wf_measure`, and `measure` will correspond to Lean/Mathlib
  well-founded relation and measure machinery.
- Isabelle `inductive ... => bool` relations will be represented as Lean
  predicates of type `Trm V -> Trm V -> Prop`.
- Isabelle `fun` equations become Lean structurally recursive definitions with
  `[simp]` evaluation theorems where the rewrite direction is unambiguous.

### Proposed Lean file mapping

- `LambdaEnv/Syntax.lean`: raw terms, `Trm.length`, and length-only arithmetic
  lemmas.
- `LambdaEnv/Relations.lean`: reusable relation notions such as joinability,
  local confluence, confluence, normal forms, and Newman-style lemmas if Mathlib
  does not provide the exact form needed.
- `LambdaEnv/Reduction.lean`: `sigma_step`, `sigma_root_step`, `beta_step`,
  `weak_step`, and their reflexive-transitive closures.
- `LambdaEnv/SigmaNormalization.lean`: sigma termination, confluence, normal
  forms, syntactic characterization, and `sigma_normalize`.
- `LambdaEnv/ParallelReduction.lean`: `term_star`, `par_step`, and Lemmas
  3.9-3.13.
- `LambdaEnv/Confluence.lean`: beta modulo sigma, Hardin interpretation, and
  final confluence theorems.

## Completed definitions

- `Trm`, corresponding to Isabelle `'v trm`.
- `Trm.length`, corresponding to Isabelle `term_length`.
- `SigmaStep`, corresponding to Isabelle `sigma_step`.
- `SigmaRootStep`, corresponding to Isabelle `sigma_root_step`.
- `Terminating`, corresponding to Isabelle `terminating`.
- `SigmaSteps`, corresponding to Isabelle `sigma_steps`.
- `BetaStep`, corresponding to Isabelle `beta_step`.
- `BetaSteps`, corresponding to Isabelle `beta_steps`.
- `WeakStep`, corresponding to Isabelle `weak_step`.
- `WeakSteps`, corresponding to Isabelle `weak_steps`.
- `Joinable`, corresponding to Isabelle `joinablep`.
- `LocallyConfluent`, corresponding to Isabelle `locally_confluentp`.
- `NormalFormFor`, corresponding to Isabelle `normal_form_for`.
- `NormalFor`, the unary no-successor predicate used by `SigmaNormal`.
- `SigmaNormal`, corresponding to Isabelle `sigma_normal`.
- `SigmaNormalForm`, corresponding to Isabelle `sigma_normal_form`.

## Completed lemmas

- `Trm.length_var`, `Trm.length_lam`, `Trm.length_app`,
  `Trm.length_id`, `Trm.length_ext`, `Trm.length_comp`.
- `Trm.length_pos`.
- `Trm.length_right_lt_comp`.
- `Trm.add_mul_right_lt_mono`.
- `Trm.add_mul_left_lt_mono`.
- `Trm.length_comp_sub_left_ext`.
- `Trm.length_comp_sub_right_ext`.
- `Trm.length_comp_sub_left_app`.
- `Trm.length_comp_sub_right_app`.
- `Trm.length_comp_sub_lamcomp_arg`.
- `Trm.length_comp_sub_varcomp_arg`.
- `SigmaRootStep.toSigmaStep`.
- `SigmaStep.length_decreases`.
- `SigmaStep.terminating`.
- `SigmaStep.toSteps`.
- `SigmaSteps.refl`, `SigmaSteps.trans`.
- `SigmaSteps.app_left`, `SigmaSteps.app_right`, `SigmaSteps.lam`.
- `SigmaSteps.comp_left`, `SigmaSteps.comp_right`.
- `SigmaSteps.ext_left`, `SigmaSteps.ext_right`.
- `SigmaSteps.comp_idRight_in_compRight`.
- `SigmaSteps.ext_comp_idRight`.
- `SigmaSteps.app_comp_idRight`.
- `locallyConfluent_of_local_peaks`.
- `Joinable.intro`, `Joinable.refl`, `Joinable.symm`.
- `SigmaJoin.steps`, `SigmaJoin.refl`, `SigmaJoin.symm`.
- `SigmaJoin.step_left`, `SigmaJoin.step_right`.
- `SigmaStep.no_id`, `SigmaStep.no_var`, `SigmaStep.ext_cases`.
- `SigmaJoin.app_left`, `SigmaJoin.app_right`, `SigmaJoin.lam`.
- `SigmaJoin.comp_left`, `SigmaJoin.comp_right`.
- `SigmaJoin.ext_left`, `SigmaJoin.ext_right`.
- `SigmaLocalPeak.app_left_right`.
- `SigmaLocalPeak.comp_left_right`.
- `SigmaLocalPeak.ext_left_right`.
- `SigmaRootStep.local_peak_joinable`.
- `SigmaLocalPeak.id`, `SigmaLocalPeak.var`.
- `SigmaLocalPeak.lam`, `SigmaLocalPeak.app`, `SigmaLocalPeak.ext`.
- `SigmaLocalPeak.comp`.
- Root/compatibility basic peaks:
  `SigmaLocalPeak.ass_left`, `ass_mid`, `ass_right`,
  `idLeft_arg`, `idRight_arg`,
  `distExt_left`, `distExt_mid`, `distExt_right`,
  `varRef_left`, `varRef_right`,
  `varSkip_left`, `varSkip_right`,
  `distApp_left`, `distApp_mid`, `distApp_right`.
- Root/compatibility packaged peaks:
  `SigmaLocalPeak.varRef_inner`, `varSkip_inner`,
  `idLeft`, `idRight`, `varRef`, `varSkip`,
  `distExt_inner`, `distExt`, `distApp_inner`, `distApp`.
- Inversion helper: `SigmaStep.app_cases`.
- Ass nested peaks:
  `SigmaLocalPeak.ass_inner_ass`, `ass_inner_idLeft`,
  `ass_inner_idRight`, `ass_inner_distExt`, `ass_inner_varRef`,
  `ass_inner_varSkip`, `ass_inner_distApp`, `ass_inner_root`,
  `ass_inner`, and `ass`.
- Whole local peak and local confluence:
  `SigmaStep.local_peak_joinable`, `SigmaStep.locallyConfluent`.
- `SigmaStep.toWeakStep`.
- `BetaStep.toWeakStep`.
- `WeakStep.sigma_or_beta`.
- `SigmaSteps.toWeakSteps`.
- `BetaSteps.toWeakSteps`.
- `no_step_reflTransGen_eq`.
- `normalFormFor_exists_of_wellFounded`.
- `SigmaNormalForm.exists`.
- `SigmaNormalForm.steps`.
- `SigmaNormalForm.normal`.
- `SigmaNormalForm.of_steps_normal`.
- `SigmaNormal.normal_form_self`.
- `Confluent`.
- `newman`.
- `SigmaStep.confluent`.
- `NormalFor.eq_of_reflTransGen`.
- `SigmaNormal.eq_of_steps`.
- `SigmaNormalForm.unique`.
- `sigmaNormalize`.
- `sigmaNormalize_normalForm`.
- `sigmaNormalize_steps`.
- `sigmaNormalize_normal`.
- `sigmaNormalize_eq_of_normalForm`.
- `sigmaNormalize_eq_of_normal`.
- `SigmaSteps.to_normalForm`.
- `sigmaNormalize_eq_of_steps`.
- `sigmaNormalize_eq_of_step`.

## In progress

- Continue with later sigma-normal syntactic characterization and downstream
  star/parallel reduction sections.

## Reduction relations audit

### Already ported

- Definitions/relations: `sigma_step`, `sigma_root_step`, `terminating`,
  `sigma_steps`, `beta_step`, `beta_steps`, `weak_step`, `weak_steps`,
  `joinablep`, `locally_confluentp`.
- Introduction/inclusion lemmas:
  `sigma_root_step_imp_sigma_step`, `sigma_step_decreases_length`,
  `sigma_step_terminating`, `sigma_step_rtranclp`,
  `sigma_step_imp_weak_step`, `beta_step_imp_weak_step`,
  `weak_step_imp_sigma_or_beta_step`,
  `sigma_steps_imp_weak_steps`, `beta_steps_imp_weak_steps`.
- Multi-step compatibility:
  `sigma_steps_app_left`, `sigma_steps_app_right`, `sigma_steps_lam`,
  `sigma_steps_comp_left`, `sigma_steps_comp_right`,
  `sigma_steps_ext_left`, `sigma_steps_ext_right`.
- Basic join/compatibility helpers:
  `sigma_join_stepsI`, `sigma_join_refl`, `sigma_join_sym`,
  `sigma_join_step_left`, `sigma_join_step_right`,
  `sigma_join_app_left`, `sigma_join_app_right`, `sigma_join_lam`,
  `sigma_join_comp_left`, `sigma_join_comp_right`,
  `sigma_join_ext_left`, `sigma_join_ext_right`,
  and compatibility-vs-compatibility local peaks for app/comp/ext.

### Not yet ported

- Joinable wrapper corresponding to `sigma_root_step_local_peak_joinablep`
  can now be a direct use of `SigmaRootStep.local_peak_joinable`.
- The Isabelle intermediate wrappers `sigma_root_vs_step_peak_joinable`,
  `sigma_step_vs_root_peak_joinable`, and `sigma_step_local_peak_from_*` are
  represented in Lean by the constructor-specific `SigmaLocalPeak.*` lemmas and
  the structural theorem `SigmaStep.local_peak_joinable`.

### Compatibility and local peak proof plan

- Root/root peak joinability is proved by case analysis on `SigmaRootStep`;
  witnesses are either reflexive, one sigma step, or one of the existing
  id-right multi-step helpers.
- Prove compatibility/compatibility peaks for each constructor.  App, comp, and
  ext two-sided peaks are already present; lam and same-side peaks reduce via
  `SigmaJoin.*` lifting.
- Prove root/compatibility peak lemmas in small groups:
  associativity, id-left/id-right, extension distribution, variable lookup/skip,
  and application distribution.
- Package the grouped lemmas into the whole-term local peak theorem only after
  the smaller cases build cleanly.

## Completed local peak cases

- root/root: `SigmaRootStep.local_peak_joinable`.
- compatibility/compatibility:
  `SigmaLocalPeak.app_left_right`, `comp_left_right`, `ext_left_right`.
- syntax-level non-root peaks:
  `SigmaLocalPeak.id`, `var`, `lam`, `app`, `ext`.
- root/compatibility direct subterm peaks:
  associativity left/middle/right, id-left/id-right argument,
  extension distribution left/middle/right, var-ref left/right, var-skip
  left/right, and application distribution left/middle/right.
- Ass nested peaks:
  outer Ass against inner Ass, IdL, IdR, DistExt, VarRef, VarSkip, and DApp;
  these are packaged through `SigmaLocalPeak.ass_inner_root`,
  `SigmaLocalPeak.ass_inner`, and `SigmaLocalPeak.ass`.
- constructor-level comp peaks: `SigmaLocalPeak.comp`.

## Completed Ass nested peaks

- `sigma_peak_Ass_inner_Ass` ↔ `SigmaLocalPeak.ass_inner_ass`.
- `sigma_peak_Ass_inner_IdL` ↔ `SigmaLocalPeak.ass_inner_idLeft`.
- `sigma_peak_Ass_inner_IdR` ↔ `SigmaLocalPeak.ass_inner_idRight`.
- `sigma_peak_Ass_inner_DExtn` ↔ `SigmaLocalPeak.ass_inner_distExt`.
- `sigma_peak_Ass_inner_VarRef` ↔ `SigmaLocalPeak.ass_inner_varRef`.
- `sigma_peak_Ass_inner_VarSkip` ↔ `SigmaLocalPeak.ass_inner_varSkip`.
- `sigma_peak_Ass_inner_DApp` ↔ `SigmaLocalPeak.ass_inner_distApp`.
- `sigma_peak_Ass_inner_root` ↔ `SigmaLocalPeak.ass_inner_root`.
- `sigma_peak_Ass_inner` ↔ `SigmaLocalPeak.ass_inner`.
- `sigma_peak_Ass` ↔ `SigmaLocalPeak.ass`.

## Completed local confluence results

- `sigma_step_local_peak_joinable` ↔ `SigmaStep.local_peak_joinable`.
- `sigma_step_locally_confluent` ↔ `SigmaStep.locallyConfluent`.

## Completed confluence results

- Local confluence is complete: `SigmaStep.locallyConfluent`.
- Newman-style global confluence is complete through the general theorem
  `newman`.
- Sigma confluence is complete: `SigmaStep.confluent`.

## Newman lemma design

- Implemented locally as the general theorem `newman` in
  `SigmaNormalization.lean`; Mathlib has `Relation.church_rosser`, but not a
  directly matching terminating plus local-confluence Newman theorem.
- The well-founded relation orientation is
  `WellFounded (fun N M => r M N)`, matching the existing
  `Terminating r` and Isabelle's `wf {(N, M). r M N}`.
- The conclusion is `Confluent r`, i.e. common-source
  `Relation.ReflTransGen r` branches are joinable by
  `Relation.ReflTransGen r`.

## Sigma normalization design

- `SigmaNormalForm.exists` is constructive from `SigmaStep.terminating`.
- `sigmaNormalize` is defined after confluence and uniqueness as a
  `noncomputable def` using `Classical.choose (SigmaNormalForm.exists M)`.
- This mirrors Isabelle's `THE`-based `sigma_normalize`: existence supplies a
  representative, and `SigmaNormalForm.unique` proves the representative is
  independent of the choice.

## Completed normal form uniqueness results

- `NormalFor.eq_of_reflTransGen`: a normal element can only reduce by
  reflexive-transitive closure to itself.
- `SigmaNormal.eq_of_steps`: sigma-normal terms have only reflexive sigma
  multi-step reducts.
- `SigmaNormalForm.unique`: sigma normal forms from the same source are unique,
  using `SigmaStep.confluent`.

## Remaining Isabelle sections

- Remainder of `Reduction relations`
- `Sigma reduction`
- `Normal forms`
- `Star transformation`
- `Parallel reduction and Lemmas 3.11-3.13`
- `Beta modulo sigma and Lemmas 3.14-3.15`
- `Hardin interpretation and Theorem 3.16`

## Design decisions

- Isabelle type variable `'v` is represented as Lean universe-polymorphic
  `V : Type u`.
- The existing constructor mapping is semantically correct and was kept:
  `TVar/TLam/TApp/TId/TExt/TComp` correspond to
  `Trm.var/Trm.lam/Trm.app/Trm.id/Trm.ext/Trm.comp`.
- `term_length` is ported as `Trm.length` rather than a top-level function so
  term-specific operations stay grouped under `Trm`.
- The six constructor equations for `Trm.length` are marked `[simp]`; the
  monotonicity and subterm-length lemmas are not marked `[simp]` because they
  are proof tools rather than canonical simplifications.
- `Mathlib.Tactic` is imported in `Syntax.lean` for Nat arithmetic automation
  used by the length lemmas.
- Isabelle `rtranclp` is represented by Mathlib
  `Relation.ReflTransGen`; the section-specific closure names
  `SigmaSteps`, `BetaSteps`, and `WeakSteps` are aliases over it.
- Reduction constructors are declared with explicit term arguments.  This avoids
  Lean auto-implicit arguments hiding the source terms during induction and
  keeps the rules close to their Isabelle counterparts.

## Isabelle to Lean correspondence

- `'v trm` ↔ `Trm V`
- `TVar` ↔ `Trm.var`
- `TLam` ↔ `Trm.lam`
- `TApp` ↔ `Trm.app`
- `TId` ↔ `Trm.id`
- `TExt` ↔ `Trm.ext`
- `TComp` ↔ `Trm.comp`
- `term_length` ↔ `Trm.length`
- `sigma_step` ↔ `SigmaStep`
- `sigma_root_step` ↔ `SigmaRootStep`
- `terminating` ↔ `Terminating`
- `rtranclp sigma_step` / `sigma_steps` ↔ `SigmaSteps`
- `beta_step` ↔ `BetaStep`
- `rtranclp beta_step` / `beta_steps` ↔ `BetaSteps`
- `weak_step` ↔ `WeakStep`
- `rtranclp weak_step` / `weak_steps` ↔ `WeakSteps`
- `joinablep` ↔ `Joinable`
- `locally_confluentp` ↔ `LocallyConfluent`
- `normal_form_for` ↔ `NormalFormFor`
- `sigma_normal` ↔ `SigmaNormal`
- `sigma_normal_form` ↔ `SigmaNormalForm`
- `no_step_rtranclp_eq` ↔ `no_step_reflTransGen_eq`
- `sigma_normal_form_exists` ↔ `SigmaNormalForm.exists`
- `sigma_root_step_local_peak_joinable` ↔
  `SigmaRootStep.local_peak_joinable`
- `sigma_peak_Ass_left/mid/right` ↔
  `SigmaLocalPeak.ass_left/mid/right`
- `sigma_peak_IdL_arg` ↔ `SigmaLocalPeak.idLeft_arg`
- `sigma_peak_IdR_arg` ↔ `SigmaLocalPeak.idRight_arg`
- `sigma_peak_DExtn_left/mid/right` ↔
  `SigmaLocalPeak.distExt_left/mid/right`
- `sigma_peak_VarRef_left/right` ↔
  `SigmaLocalPeak.varRef_left/right`
- `sigma_peak_VarSkip_left/right` ↔
  `SigmaLocalPeak.varSkip_left/right`
- `sigma_peak_DApp_left/mid/right` ↔
  `SigmaLocalPeak.distApp_left/mid/right`
- `sigma_peak_VarRef_inner` ↔ `SigmaLocalPeak.varRef_inner`
- `sigma_peak_VarSkip_inner` ↔ `SigmaLocalPeak.varSkip_inner`
- `sigma_peak_IdL` ↔ `SigmaLocalPeak.idLeft`
- `sigma_peak_IdR` ↔ `SigmaLocalPeak.idRight`
- `sigma_peak_VarRef` ↔ `SigmaLocalPeak.varRef`
- `sigma_peak_VarSkip` ↔ `SigmaLocalPeak.varSkip`
- `sigma_step_TApp_cases` partial counterpart ↔ `SigmaStep.app_cases`
- `sigma_peak_DExtn_inner` ↔ `SigmaLocalPeak.distExt_inner`
- `sigma_peak_DExtn` ↔ `SigmaLocalPeak.distExt`
- `sigma_peak_DApp_inner` ↔ `SigmaLocalPeak.distApp_inner`
- `sigma_peak_DApp` ↔ `SigmaLocalPeak.distApp`
- `sigma_peak_Ass_inner_Ass` ↔ `SigmaLocalPeak.ass_inner_ass`
- `sigma_peak_Ass_inner_IdL` ↔ `SigmaLocalPeak.ass_inner_idLeft`
- `sigma_peak_Ass_inner_IdR` ↔ `SigmaLocalPeak.ass_inner_idRight`
- `sigma_peak_Ass_inner_DExtn` ↔ `SigmaLocalPeak.ass_inner_distExt`
- `sigma_peak_Ass_inner_VarRef` ↔ `SigmaLocalPeak.ass_inner_varRef`
- `sigma_peak_Ass_inner_VarSkip` ↔ `SigmaLocalPeak.ass_inner_varSkip`
- `sigma_peak_Ass_inner_DApp` ↔ `SigmaLocalPeak.ass_inner_distApp`
- `sigma_peak_Ass_inner_root` ↔ `SigmaLocalPeak.ass_inner_root`
- `sigma_peak_Ass_inner` ↔ `SigmaLocalPeak.ass_inner`
- `sigma_peak_Ass` ↔ `SigmaLocalPeak.ass`
- `sigma_step_local_peak_joinable` ↔ `SigmaStep.local_peak_joinable`
- `sigma_step_locally_confluent` ↔ `SigmaStep.locallyConfluent`
- `confluentp` ↔ `Confluent`
- `newman_lemma` ↔ `newman`
- `sigma_step_confluent` ↔ `SigmaStep.confluent`
- `unique_normal_form` / `sigma_normal_form_unique` ↔
  `SigmaNormalForm.unique`
- `sigma_normalize` ↔ `sigmaNormalize`
- `sigma_nf_normal_form` ↔ `sigmaNormalize_normalForm`
- `sigma_nf_steps` ↔ `sigmaNormalize_steps`
- `sigma_nf_normal` ↔ `sigmaNormalize_normal`
- `sigma_normalize_eq_if_normal_form` ↔
  `sigmaNormalize_eq_of_normalForm`
- `sigma_normalize_eq_of_sigma_steps` ↔
  `sigmaNormalize_eq_of_steps`

## Build status

- Command:
  `lake build`
- Result:
  success
- Last checked:
  2026-07-13 Asia/Tokyo

## Sigma normalization declaration order

- `sigmaNormalize` and its normal-form, uniqueness, and closure lemmas now
  precede all lemmas that invoke `sigmaNormalize`.
- No theorem statement was changed; the move only resolves Lean's
  forward-reference errors.

## Remaining sigma lemmas

- Isabelle theorem: `sigma_normal_imp_sigma_normal_syntax_corrected`,
  `sigma_normal_syntax_corrected_imp_sigma_normal`,
  `lemma_3_7_sigma_normal_syntactic_characterization`
  Lean theorem: `sigma_normal_syntax_corrected` only
  Status: remaining
  Needed by: the original Isabelle proof of `sigma_normal_TComp_cases_for_par_refl`;
  Lean already has a direct case-analysis helper for that immediate use.

- Isabelle theorem: `sigma_normalize_comp_right_normalize`,
  `sigma_normalize_comp_left_normalize`
  Lean theorem: not yet ported
  Status: remaining
  Needed by: composition congruence in Lemma 3.11 and beta-modulo-sigma proofs.

- Isabelle theorem: `sigma_normalize_comp_var_ext_same`,
  `sigma_normalize_comp_var_ext_diff`, `sigma_normalize_comp_app`,
  `sigma_normalize_comp_comp`, `sigma_normalize_comp_lam`,
  `sigma_normalize_comp_var_not_ext`
  Lean theorem: not yet ported
  Status: remaining
  Needed by: the detailed parallel-composition and strong-confluence cases.

- Isabelle theorem: `sigma_normalize_if_sigma_normal`
  Lean theorem: `sigmaNormalize_eq_of_normal`
  Status: complete
  Needed by: star normalization and every downstream normalization rewrite.

- Isabelle theorem: `sigma_normalize_lam`, `sigma_normalize_app`,
  `sigma_normalize_ext`, `sigma_normalize_comp_id_left`,
  `sigma_normalize_comp_id_right`, `sigma_normalize_comp_lam_id`,
  `sigma_normalize_comp_lam_not_id`, `sigma_normalize_comp_ext`
  Lean theorem: corresponding `sigma_normalize_*` names
  Status: complete
  Needed by: parallel-reduction normalization calculations.

## Term star

- `Trm.star` is implemented in `LambdaEnv/ParallelReduction.lean` with all
  eleven Isabelle `term_star` clauses in source order.
- Complete: constructor/equation lemmas through `term_star_var_comp`,
  `term_star_sigma_normal`, and `sigma_normalize_term_star_eq`.
- The source has no separate `term_star` idempotence theorem; no conjectural
  replacement was added.

## Parallel reduction rules

| Isabelle | Lean | Side conditions |
|---|---|---|
| `ParVar` | pending `ParStep.var` | none |
| `ParLam` | pending `ParStep.lam` | recursive premise |
| `ParApp` | pending `ParStep.app` | two recursive premises |
| `ParId` | pending `ParStep.id` | none |
| `ParExtn` | pending `ParStep.ext` | two recursive premises |
| `ParLamComp` | pending | `V ≠ TId`, `V' ≠ TId` |
| `ParLamCompId` | pending | `par_step V TId`, `V ≠ TId` |
| `ParVarComp` | pending | `not_ext W`, `not_ext W'`, `W ≠ TId`, `W' ≠ TId` |
| `ParVarCompOther` | pending | `not_ext W`, `¬ not_ext W'`, `W ≠ TId`, and Isabelle lists `W' ≠ TId` twice |
| `ParVarCompId` | pending | `par_step W TId`, `not_ext W`, `W ≠ TId` |
| `ParBeta1` | pending | recursive premises for body and argument |
| `ParBeta2` | pending | `W ≠ TId` plus recursive premises for body, argument, environment |

## Current goal

Complete the next sigma composition-normalization lemmas required before the
parallel reduction congruence and strong-confluence proofs.

## Remaining work

- Port the remaining sigma lemmas listed above, beginning with normalization
  under composition.
- Define `ParStep` exactly as surveyed, then establish its source/target
  sigma-normality lemmas.
- Continue with Lemmas 3.11--3.13 and beta modulo sigma only after those
  prerequisites build.

## Build status

- Command: `lake env lean LambdaEnv/ParallelReduction.lean`
- Result: success
- Last checked: 2026-07-13 Asia/Tokyo
