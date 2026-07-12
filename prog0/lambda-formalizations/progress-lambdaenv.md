# LambdaEnv Lean 4 Port Progress

## Current goal

Port `IsabelleSources/LambdaEnv.thy` to Lean 4 in dependency order.  The first
completed slice is `section "Raw terms and length"` plus the length-only helper
lemmas that immediately support later reduction termination proofs.

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

## In progress

- Next section: `Reduction relations`, starting with `sigma_step` and
  `sigma_root_step`.

## Remaining Isabelle sections

- `Reduction relations`
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

## Isabelle to Lean correspondence

- `'v trm` ↔ `Trm V`
- `TVar` ↔ `Trm.var`
- `TLam` ↔ `Trm.lam`
- `TApp` ↔ `Trm.app`
- `TId` ↔ `Trm.id`
- `TExt` ↔ `Trm.ext`
- `TComp` ↔ `Trm.comp`
- `term_length` ↔ `Trm.length`

## Build status

- Command:
  `lake build`
- Result:
  success
- Last checked:
  2026-07-13 Asia/Tokyo
