/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StackJointAgreement

/-!
# ℓ-ary (curve) mutual correlated agreement: `mcaEventCurve` and `epsMCACurve`

The ABF26 mutual-correlated-agreement event `mcaEvent` and error `epsMCA`
(`ProximityGap/Errors.lean`) are `Fin 2`-only (the affine-line case `u₀ + γ·u₁`). This file
provides the **ℓ-ary curve generalization** — the combiner is the polynomial curve
`∑ j, γ^j • uⱼ` over an `L`-row word stack — which is the MCA event family matching the
`parℓ > 2` power generator of WHIR (`RSGenerator.genRSC`) and the "powers of z" general
combinations of Hab25 (ePrint 2025/2110, remark after Theorem 2):

* `stackJointAgreesOn` — imported row-index-general `pairJointAgreesOn`: a full stack of
  codewords agrees with `u` row-wise on `S`;
* `mcaEventCurve` — `L`-ary `mcaEvent`: a witness set `S` of size `≥ (1−δ)·n` on which the
  curve `∑ j, γ^j • uⱼ` equals some codeword, while no codeword stack jointly agrees with
  `u` on `S`;
* `epsMCACurve` — `L`-ary `epsMCA`: the sup over `L`-row stacks of the uniform-`γ`
  probability of `mcaEventCurve`;
* pair-compatibility: at `L = 2` the curve notions coincide with the affine-line notions
  (`stackJointAgreesOn_pair_iff`, `mcaEventCurve_pair_iff`, `epsMCACurve_two_eq_epsMCA`),
  so `epsMCACurve` is a genuine extension, not a fork;
* basic facts mirroring the pair API: `epsMCACurve_le_one`, `epsMCACurve_mono`,
  `mcaEventCurve_imp_relCloseToCode`.

The WHIR-side consumer is `ArkLib/ProofSystem/Whir/MCACurveSeam.lean`, which feeds
`epsMCACurve` bounds into `hasMutualCorrAgreement` for the `parℓ = Fin L` power generator.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The `L`-ary curve MCA bad event** (ABF26 Definition 4.3, curve/power-combiner form):
there is a witness set `S` of size at least `(1−δ)·n` on which the polynomial curve
`∑ j, γ^j • u j` exactly equals some codeword of `C`, but no stack of codewords jointly
agrees with `u` on `S`. At `L = 2` this is `mcaEvent` (see `mcaEventCurve_pair_iff`). -/
def mcaEventCurve (C : Set (ι → A)) (δ : ℝ≥0) {L : ℕ} (u : Fin L → ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = ∑ j : Fin L, γ ^ (j : ℕ) • u j i) ∧
    ¬ stackJointAgreesOn C S u

open Classical in
/-- **The `L`-ary curve MCA error** (ABF26 Definition 4.3, curve form): the worst-case
probability over `L`-row word stacks `u` and uniform `γ ← $ᵖ F` of `mcaEventCurve`.
At `L = 2` this is `epsMCA` (see `epsMCACurve_two_eq_epsMCA`). -/
noncomputable def epsMCACurve (C : Set (ι → A)) (L : ℕ) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin L) ι,
    Pr_{let γ ← $ᵖ F}[mcaEventCurve C δ u γ]

/-! ## Pair compatibility: `L = 2` recovers the affine-line notions -/

/-- The two-row curve `∑ j : Fin 2, γ^j • u j` is the affine line `u 0 + γ • u 1`. -/
theorem curve_two_eq_line (u : Fin 2 → ι → A) (γ : F) (i : ι) :
    (∑ j : Fin 2, γ ^ (j : ℕ) • u j i) = u 0 i + γ • u 1 i := by
  rw [Fin.sum_univ_two]
  simp

/-- At `L = 2`, `mcaEventCurve` is `mcaEvent`. -/
theorem mcaEventCurve_pair_iff (C : Set (ι → A)) (δ : ℝ≥0) (u : Fin 2 → ι → A) (γ : F) :
    mcaEventCurve C δ u γ ↔ mcaEvent C δ (u 0) (u 1) γ := by
  constructor
  · rintro ⟨S, hcard, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun h => hno ((stackJointAgreesOn_pair_iff C S u).mpr h)⟩
    rw [hweq i hi]
    exact curve_two_eq_line u γ i
  · rintro ⟨S, hcard, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hcard, ⟨w, hw, fun i hi => ?_⟩,
      fun h => hno ((stackJointAgreesOn_pair_iff C S u).mp h)⟩
    rw [hweq i hi]
    exact (curve_two_eq_line u γ i).symm

open Classical in
/-- At `L = 2`, the curve MCA error **is** the affine-line MCA error `epsMCA`:
the generalization is conservative. -/
theorem epsMCACurve_two_eq_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCACurve (F := F) C 2 δ = epsMCA (F := F) C δ := by
  unfold epsMCACurve epsMCA
  refine iSup_congr fun u => ?_
  refine le_antisymm
    (Pr_le_Pr_of_implies _ _ _ fun γ h => (mcaEventCurve_pair_iff C δ u γ).mp h)
    (Pr_le_Pr_of_implies _ _ _ fun γ h => (mcaEventCurve_pair_iff C δ u γ).mpr h)

/-! ## Basic facts mirroring the pair API -/

open Classical in
/-- The curve MCA error is bounded by the total probability mass. -/
theorem epsMCACurve_le_one (C : Set (ι → A)) (L : ℕ) (δ : ℝ≥0) :
    epsMCACurve (F := F) C L δ ≤ 1 := by
  unfold epsMCACurve
  refine iSup_le fun u => ?_
  exact Pr_le_one ($ᵖ F) fun γ => mcaEventCurve C δ u γ

open Classical in
/-- **`epsMCACurve` is monotone in `δ`** — the `L`-ary analogue of `epsMCA_mono`: a larger
radius only weakens the size constraint `|S| ≥ (1 − δ)·n`; the other clauses are `δ`-free. -/
theorem epsMCACurve_mono (C : Set (ι → A)) (L : ℕ) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCACurve (F := F) C L δ ≤ epsMCACurve (F := F) C L δ' := by
  unfold epsMCACurve
  refine iSup_mono fun u => ?_
  refine Pr_le_Pr_of_implies _ _ _ fun γ h_event => ?_
  obtain ⟨S, hS_card, hline, hstack⟩ := h_event
  exact ⟨S, le_trans (mul_le_mul_of_nonneg_right (tsub_le_tsub_left h 1) (zero_le _)) hS_card,
    hline, hstack⟩

/-- The `mcaEventCurve` always entails that the curve `∑ j, γ^j • u j` is `δ`-close to `C`
(the `L`-ary analogue of `mcaEvent_imp_relCloseToCode`): the witness set carries a codeword
agreeing with the curve on a `(1−δ)`-fraction of positions. -/
theorem mcaEventCurve_imp_relCloseToCode
    (C : Set (ι → A)) (δ : ℝ≥0) {L : ℕ} (u : Fin L → ι → A) (γ : F)
    (h : mcaEventCurve C δ u γ) :
    δᵣ((fun i => ∑ j : Fin L, γ ^ (j : ℕ) • u j i), C) ≤ δ := by
  classical
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, _hstack⟩ := h
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj => ?_, fun hne hj => ?_⟩
  · exact (hw_eq j hj).symm
  · exact hne ((hw_eq j hj).symm)

end ProximityGap

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ProximityGap.stackJointAgreesOn_pair_iff
#print axioms ProximityGap.curve_two_eq_line
#print axioms ProximityGap.mcaEventCurve_pair_iff
#print axioms ProximityGap.epsMCACurve_two_eq_epsMCA
#print axioms ProximityGap.epsMCACurve_le_one
#print axioms ProximityGap.epsMCACurve_mono
#print axioms ProximityGap.mcaEventCurve_imp_relCloseToCode
