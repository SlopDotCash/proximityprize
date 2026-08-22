/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `epsMCA` bad-`γ` counting glue (structural reduction for ABF26 Theorem 5.1)

This file isolates and proves, **kernel-clean**, the *structural* half of the reduction that
turns GCXK25's per-stack "bad combining point" counts into an `ε_mca` bound. It is the
in-tree-provable glue between

* GCXK25's combinatorial counts of `Bad(π₁,π₂,δ)` (the in-tree second-moment backbone lives
  in `Connections/GCXK25SecondMoment.lean`; the GKL24 first-moment `|Bad¹| ≤ pn` count is the
  named external residual), and
* ArkLib's `ProximityGap.epsMCA` — a supremum over **arbitrary** word stacks `u` of the
  uniform-`γ` probability of `mcaEvent` (ABF26 Definition 4.3).

## What is proven here (structural, `sorry`-free, axiom-clean)

* `mcaBad` — for a fixed stack `(u₀, u₁)`, the finset of "bad" scalars `γ ∈ F` for which the
  `mcaEvent` at radius `δ` holds.
* `mcaEvent_prob_eq_mcaBad_card_div` — the uniform-`γ` probability of `mcaEvent` equals
  `|mcaBad| / |F|` (a thin wrapper over `prob_uniform_eq_card_filter_div_card`).
* `mcaEvent_prob_le_of_mcaBad_card_le` — **per-stack counting bound**: if `|mcaBad| ≤ B` (a
  real bound `B`), then `Pr_γ[mcaEvent] ≤ ENNReal.ofReal (B / |F|)`.
* `epsMCA_le_ofReal_of_forall_mcaBad_card_le` — **the structural reduction**: if *every* stack
  has `|mcaBad| ≤ B`, then `ε_mca(C, δ) ≤ ENNReal.ofReal (B / |F|)`. This is the
  `iSup`-packaging of the per-stack bound; it reduces the entire `ε_mca` bound to a single
  uniform per-stack count of bad combining points — exactly the count GCXK25's two-part
  `|Bad¹| + |Bad²|` argument produces.

The companion file `Connections/ListDecodingAndCA.lean` wires its T5.1
`linear_listSize_to_epsMCA_gcxk25_of_residuals` to the bound proven here, surfacing the
residual as the per-stack *bad-`γ`-count* bound `|mcaBad u| ≤ L²·δ·n + 1/η` (the genuine
GCXK25 amplification content), rather than as a raw probability hypothesis.

## What this file does *not* close

It does **not** supply the per-stack count `|mcaBad u| ≤ L²·δ·n + 1/η` itself. That count is
GCXK25's amplification (their `|Bad¹| ≤ pn` GKL24 first-moment lemma plus the in-tree
`|Bad²| < 1/ε` second-moment count and the `L²` list-size factor), which is *not* connected to
ArkLib's `Lambda`/`epsMCA` in-tree. This file is purely the supremum-to-count plumbing.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- For a fixed stack `(u₀, u₁)` and radius `δ`, the finset of "bad" scalars `γ ∈ F` for which
the `mcaEvent` holds. The probability `Pr_γ[mcaEvent]` is `|mcaBad| / |F|`. -/
noncomputable def mcaBad (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ)

open Classical in
/-- The uniform-`γ` probability of `mcaEvent` equals `|mcaBad| / |F|`. -/
theorem mcaEvent_prob_eq_mcaBad_card_div (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent C δ u₀ u₁ γ ] =
      ((mcaBad (F := F) C δ u₀ u₁).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  rfl

open Classical in
/-- **Per-stack counting bound.** If the number of bad scalars is at most a real bound `B`,
then `Pr_γ[mcaEvent] ≤ ENNReal.ofReal (B / |F|)`. -/
theorem mcaEvent_prob_le_of_mcaBad_card_le
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) {B : ℝ}
    (hcard : ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ B) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent C δ u₀ u₁ γ ] ≤
      ENNReal.ofReal (B / Fintype.card F) := by
  classical
  rw [mcaEvent_prob_eq_mcaBad_card_div]
  -- Move the `ℝ≥0` quotient into `ENNReal.ofReal` and use monotonicity of `ofReal`.
  set m : ℕ := (mcaBad (F := F) C δ u₀ u₁).card with hm
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- The LHS coerced to `ENNReal` equals `ENNReal.ofReal (m / |F|)`.
  have hlhs : (((m : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal)
      = ENNReal.ofReal ((m : ℝ) / Fintype.card F) := by
    rw [ENNReal.coe_nnreal_eq]
    norm_num [ENNReal.ofReal_div_of_pos hqpos]
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  rw [show ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℝ≥0) : ENNReal)
      = (((m : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) by
    rw [ENNReal.coe_div hFne]]
  rw [hlhs]
  apply ENNReal.ofReal_le_ofReal
  gcongr

open Classical in
/-- **The structural reduction (ABF26 §5 supremum-to-count plumbing).** If *every* stack
`u : WordStack A (Fin 2) ι` has at most `B` bad combining points (`|mcaBad (u 0) (u 1)| ≤ B`),
then `ε_mca(C, δ) ≤ ENNReal.ofReal (B / |F|)`.

This is the `iSup`-packaging of `mcaEvent_prob_le_of_mcaBad_card_le`: it reduces the whole
`ε_mca` bound — a supremum over arbitrary word stacks — to a single *uniform* per-stack count
of bad scalars `γ`. That count is exactly what GCXK25's two-part `|Bad¹| + |Bad²|` argument
produces (the GKL24 first-moment `|Bad¹| ≤ pn` plus the in-tree second-moment `|Bad²| < 1/ε`,
times the `L²` list-size factor). -/
theorem epsMCA_le_ofReal_of_forall_mcaBad_card_le
    (C : Set (ι → A)) (δ : ℝ≥0) {B : ℝ}
    (hcard : ∀ u : WordStack A (Fin 2) ι,
        ((mcaBad (F := F) C δ (u 0) (u 1)).card : ℝ) ≤ B) :
    epsMCA (F := F) (A := A) C δ ≤ ENNReal.ofReal (B / Fintype.card F) := by
  classical
  unfold epsMCA
  refine iSup_le fun u => ?_
  exact mcaEvent_prob_le_of_mcaBad_card_le C δ (u 0) (u 1) (hcard u)

end

end ProximityGap
