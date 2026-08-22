/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.MCACurveEvent
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# General-`parℓ` mutual correlated agreement error: `ε_mcaP`

This file lifts the `Fin 2` (affine-line) mutual correlated agreement (MCA) layer of
[`Errors.lean`](Errors.lean) to the general degree-`(parℓ−1)` *curve* case. The `Fin 2`
constructions there (`mcaEvent`, `epsMCA`) cover only the affine line `f₀ + γ·f₁`; the
file note at `Errors.lean:75` flags this as a future extension. This file is that
extension.

The combination we generalize to is the **Reed–Solomon power-generator curve**
`∑ⱼ γ^(exp j) · fⱼ`, matching `RSGenerator.genRSC`'s generator family
`Gen = { (fun j ↦ r ^ (exp j)) | r ∈ F }` (`ProximityGen.lean:87`) and the Vandermonde
form used by `MCAJohnson.curve_mutual_extract` (`MCAJohnsonCurveExtract.lean`). The
exponent map `exp : Fin parℓ → ℕ` is left general; the canonical RS choice is
`exp j = (j : ℕ)`, which recovers `∑ⱼ γ^j · fⱼ` and, at `parℓ = 2`, the affine line
`f₀ + γ·f₁`.

## Main definitions

- `ProximityGapP.curveComb` — the power-generator combination `∑ⱼ γ^(exp j) • fⱼ`.
- `ProximityGapP.pairJointAgreesOnP` — `parℓ`-ary joint agreement of a word stack with a
  codeword tuple on a witness set `S` (generalizes `ProximityGap.pairJointAgreesOn`).
- `ProximityGapP.mcaEventP` — the general-`parℓ` MCA "bad event" (generalizes
  `ProximityGap.mcaEvent`).
- `ProximityGapP.epsMCAP` — general-`parℓ` MCA error `ε_mcaP(C, exp, δ)` (generalizes
  `ProximityGap.epsMCA`).

## Main results

- `ProximityGapP.epsMCAP_mono` — monotonicity in `δ` (analogue of `ProximityGap.epsMCA_mono`).
- `ProximityGapP.pairJointAgreesOnP_iff_stackJointAgreesOn` — identifies the `epsMCAP`
  joint-agreement clause with the row-index-general stack-agreement API.
- `ProximityGapP.mcaEventP_val_iff_mcaEventCurve` — identifies the canonical exponent
  `exp j = j` specialization with `ProximityGap.mcaEventCurve`.
- `ProximityGapP.epsMCAP_val_eq_epsMCACurve` — the corresponding equality of error functions.
- `ProximityGapP.pairJointAgreesOnP_two_iff` — the `Fin 2` specialization of
  `pairJointAgreesOnP` is equivalent to `ProximityGap.pairJointAgreesOn`.
- `ProximityGapP.epsMCAP_two_eq_epsMCA` — the `Fin 2` / `exp = id` specialization of
  `epsMCAP` is exactly the existing `ProximityGap.epsMCA`.
- `ProximityGapP.Pr_proximityConditionP_le_epsMCAP` — the general-`parℓ` analogue of
  `MutualCorrAgreement.Pr_proximityCondition_le_epsMCA`: the probability over `γ ←$ᵖ F` of
  WHIR's `proximityCondition` with the power-generator `r = fun j ↦ γ^(exp j)` is bounded
  by `epsMCAP C exp δ`. This is the layer that lets WHIR-style proofs cite an MCA bound at
  *general* `parℓ`, not just `Fin 2`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- [ACFY24] Arnon, Chiesa, Fenzi, Yogev. *WHIR*. 2024.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGapP

open NNReal Code
open scoped ProbabilityTheory BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The **Reed–Solomon power-generator curve** combination `∑ⱼ γ^(exp j) • fⱼ` of a
`parℓ`-ary word stack `u : WordStack A (Fin parℓ) ι` at scalar `γ`. With `exp j = (j : ℕ)`
this is `∑ⱼ γ^j • uⱼ`, the Vandermonde form of `RSGenerator.genRSC`; at `parℓ = 2` it
is the affine line `u 0 + γ • u 1`. -/
def curveComb {parℓ : ℕ} (exp : Fin parℓ → ℕ) (u : WordStack A (Fin parℓ) ι) (γ : F) :
    ι → A :=
  fun i => ∑ j : Fin parℓ, (γ ^ (exp j)) • u j i

/-- `parℓ`-ary joint agreement: there is a tuple of codewords `v : Fin parℓ → (ι → A)` of
`C` agreeing with the corresponding rows of the stack `u` on every position of `S`.
Generalizes `ProximityGap.pairJointAgreesOn` (the `parℓ = 2` case). Equivalent in spirit to
`Δ_S(u, C^≡ parℓ) = 0`. -/
def pairJointAgreesOnP {parℓ : ℕ} (C : Set (ι → A)) (S : Finset ι)
    (u : WordStack A (Fin parℓ) ι) : Prop :=
  ∃ v : Fin parℓ → ι → A, (∀ j, v j ∈ C) ∧ ∀ i ∈ S, ∀ j, v j i = u j i

/-- The **general-`parℓ` MCA bad event** (generalizes `ProximityGap.mcaEvent`). There is a
witness set `S` of size `≥ (1-δ)·n` on which the power-generator curve `∑ⱼ γ^(exp j)·uⱼ`
exactly equals some codeword of `C`, but no tuple of codewords agrees with the stack `u`
jointly on `S`. -/
def mcaEventP {parℓ : ℕ} (C : Set (ι → A)) (exp : Fin parℓ → ℕ) (δ : ℝ≥0)
    (u : WordStack A (Fin parℓ) ι) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = curveComb exp u γ i) ∧
    ¬ pairJointAgreesOnP C S u

open Classical in
/-- **General-`parℓ` mutual correlated agreement error** `ε_mcaP(C, exp, δ)`. Worst-case
probability over `parℓ`-ary word stacks `u` and `γ ←$ᵖ F` of the `mcaEventP`. Generalizes
`ProximityGap.epsMCA` (`Fin 2`, `exp = id`). -/
noncomputable def epsMCAP {parℓ : ℕ} (C : Set (ι → A)) (exp : Fin parℓ → ℕ) (δ : ℝ≥0) :
    ENNReal :=
  ⨆ u : WordStack A (Fin parℓ) ι,
    Pr_{let γ ← $ᵖ F}[mcaEventP C exp δ u γ]

/-! ## Bridges to the row-index-general stack and curve MCA APIs -/

/-- The `pairJointAgreesOnP` predicate is definitionally the same row-index-general
stack-agreement predicate as `ProximityGap.stackJointAgreesOn`. This bridge lets
`epsMCAP` arguments reuse the rowwise product API from `StackJointAgreement.lean`. -/
theorem pairJointAgreesOnP_iff_stackJointAgreesOn {parℓ : ℕ}
    (C : Set (ι → A)) (S : Finset ι) (u : WordStack A (Fin parℓ) ι) :
    pairJointAgreesOnP C S u ↔ ProximityGap.stackJointAgreesOn C S u := by
  rfl

/-- Rowwise split for `pairJointAgreesOnP`: a stack agrees jointly on `S` iff each row
independently has a codeword agreeing with it on `S`. -/
theorem pairJointAgreesOnP_iff_forall_row {parℓ : ℕ}
    (C : Set (ι → A)) (S : Finset ι) (u : WordStack A (Fin parℓ) ι) :
    pairJointAgreesOnP C S u ↔ ∀ j : Fin parℓ, ∃ v ∈ C, ∀ i ∈ S, v i = u j i := by
  rw [pairJointAgreesOnP_iff_stackJointAgreesOn]
  exact ProximityGap.stackJointAgreesOn_iff_forall_row C S u

/-- A single row that cannot agree with any codeword on `S` rules out joint agreement for
the whole `pairJointAgreesOnP` stack. -/
theorem not_pairJointAgreesOnP_of_not_row {parℓ : ℕ}
    (C : Set (ι → A)) (S : Finset ι) (u : WordStack A (Fin parℓ) ι) (j : Fin parℓ)
    (hrow : ¬ ∃ v ∈ C, ∀ i ∈ S, v i = u j i) :
    ¬ pairJointAgreesOnP C S u := by
  rw [pairJointAgreesOnP_iff_stackJointAgreesOn]
  exact ProximityGap.not_stackJointAgreesOn_of_not_row C S u j hrow

/-- The old `jointAgreement` API is equivalent to the existence of a large
`pairJointAgreesOnP` witness set. -/
theorem jointAgreement_iff_exists_pairJointAgreesOnP {parℓ : ℕ}
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin parℓ) ι) :
    jointAgreement (C := C) (W := u) δ ↔
      ∃ S : Finset ι,
        (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧ pairJointAgreesOnP C S u := by
  rw [ProximityGap.jointAgreement_iff_exists_stackJointAgreesOn C δ u]
  rfl

/-- Contrapositive transport from `jointAgreement` to the `pairJointAgreesOnP` witness
shape used in `mcaEventP`. -/
theorem not_pairJointAgreesOnP_of_not_jointAgreement {parℓ : ℕ}
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin parℓ) ι) (S : Finset ι)
    (hcard : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hnja : ¬ jointAgreement (C := C) (W := u) δ) :
    ¬ pairJointAgreesOnP C S u := by
  rw [pairJointAgreesOnP_iff_stackJointAgreesOn]
  exact ProximityGap.not_stackJointAgreesOn_of_not_jointAgreement C δ u S hcard hnja

@[simp]
theorem curveComb_val_apply {parℓ : ℕ} (u : WordStack A (Fin parℓ) ι) (γ : F) (i : ι) :
    curveComb (ι := ι) (A := A) (fun j : Fin parℓ => (j : ℕ)) u γ i =
      ∑ j : Fin parℓ, γ ^ (j : ℕ) • u j i := rfl

/-- With the canonical exponent map `j ↦ j`, `curveComb` is the curve combiner used by
`ProximityGap.mcaEventCurve`. -/
theorem curveComb_val_eq_curve {parℓ : ℕ} (u : WordStack A (Fin parℓ) ι) (γ : F) :
    curveComb (ι := ι) (A := A) (fun j : Fin parℓ => (j : ℕ)) u γ =
      fun i => ∑ j : Fin parℓ, γ ^ (j : ℕ) • u j i := rfl

/-- The canonical-exponent `mcaEventP` is exactly the existing curve MCA event. -/
theorem mcaEventP_val_iff_mcaEventCurve {parℓ : ℕ}
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin parℓ) ι) (γ : F) :
    mcaEventP C (fun j : Fin parℓ => (j : ℕ)) δ u γ ↔
      ProximityGap.mcaEventCurve C δ u γ := by
  rw [mcaEventP, ProximityGap.mcaEventCurve]
  rfl

open Classical in
/-- The canonical-exponent power-generator MCA error is the curve MCA error. This is the
DRY bridge between the arbitrary-exponent `epsMCAP` API and the fixed Vandermonde-curve
`epsMCACurve` API. -/
theorem epsMCAP_val_eq_epsMCACurve {parℓ : ℕ} (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAP (F := F) C (fun j : Fin parℓ => (j : ℕ)) δ =
      ProximityGap.epsMCACurve (F := F) C parℓ δ := by
  unfold epsMCAP ProximityGap.epsMCACurve
  exact iSup_congr fun u =>
    le_antisymm
      (Pr_le_Pr_of_implies _ _ _ fun γ h =>
        (mcaEventP_val_iff_mcaEventCurve C δ u γ).mp h)
      (Pr_le_Pr_of_implies _ _ _ fun γ h =>
        (mcaEventP_val_iff_mcaEventCurve C δ u γ).mpr h)

/-- Reverse-orientation alias for callers starting from `epsMCACurve`. -/
theorem epsMCACurve_eq_epsMCAP_val {parℓ : ℕ} (C : Set (ι → A)) (δ : ℝ≥0) :
    ProximityGap.epsMCACurve (F := F) C parℓ δ =
      epsMCAP (F := F) C (fun j : Fin parℓ => (j : ℕ)) δ :=
  (epsMCAP_val_eq_epsMCACurve (F := F) C δ).symm

/-! ## Monotonicity in `δ` -/

/-- **`epsMCAP` is monotone in `δ`.** A larger proximity radius `δ` only *weakens* the size
constraint `|S| ≥ (1-δ)·n` of `mcaEventP` (the curve-agreement and joint-disagreement
clauses are `δ`-free), so the bad event holds for at least as many witness sets `S`. The
per-`u` probability grows pointwise, and so does the supremum. This is the `epsMCAP`
analogue of `ProximityGap.epsMCA_mono`. -/
theorem epsMCAP_mono {parℓ : ℕ} (C : Set (ι → A)) (exp : Fin parℓ → ℕ)
    {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCAP (F := F) C exp δ ≤ epsMCAP (F := F) C exp δ' := by
  classical
  unfold epsMCAP
  apply iSup_mono
  intro u
  apply Pr_le_Pr_of_implies
  intro γ h_event
  obtain ⟨S, hS_card, hcurve, hpair⟩ := h_event
  exact ⟨S, le_trans (mul_le_mul_of_nonneg_right (tsub_le_tsub_left h 1) (zero_le _)) hS_card,
    hcurve, hpair⟩

open Classical in
/-- The general power-generator MCA error is bounded by total probability mass. -/
theorem epsMCAP_le_one {parℓ : ℕ} (C : Set (ι → A)) (exp : Fin parℓ → ℕ) (δ : ℝ≥0) :
    epsMCAP (F := F) C exp δ ≤ 1 := by
  unfold epsMCAP
  refine iSup_le fun u => ?_
  exact ProximityGap.Pr_le_one ($ᵖ F) fun γ => mcaEventP C exp δ u γ

/-- Any `mcaEventP` witness makes the corresponding power-generator curve `δ`-close to
the code. This is the arbitrary-exponent analogue of
`ProximityGap.mcaEventCurve_imp_relCloseToCode`. -/
theorem mcaEventP_imp_relCloseToCode {parℓ : ℕ}
    (C : Set (ι → A)) (exp : Fin parℓ → ℕ) (δ : ℝ≥0)
    (u : WordStack A (Fin parℓ) ι) (γ : F)
    (h : mcaEventP C exp δ u γ) :
    δᵣ(curveComb exp u γ, C) ≤ δ := by
  classical
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, _hpair⟩ := h
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj => ?_, fun hne hj => ?_⟩
  · exact (hw_eq j hj).symm
  · exact hne ((hw_eq j hj).symm)

open Classical in
/-- Per-stack event domination: bad power-generator seeds are contained in the seeds where
the combined curve is `δ`-close to the code. -/
theorem mcaEventP_probability_le_curve_close_probability {parℓ : ℕ}
    (C : Set (ι → A)) (exp : Fin parℓ → ℕ) (δ : ℝ≥0)
    (u : WordStack A (Fin parℓ) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEventP C exp δ u γ] ≤
      Pr_{let γ ← $ᵖ F}[δᵣ(curveComb exp u γ, C) ≤ δ] := by
  exact Pr_le_Pr_of_implies _ _ _ fun γ h =>
    mcaEventP_imp_relCloseToCode C exp δ u γ h

/-! ## `Fin 2` specialization recovers the existing `epsMCA`

We take `exp j = (j : ℕ)` so that `curveComb exp u γ = u 0 + γ • u 1` (the affine line) and
show that the general-`parℓ` MCA error at `parℓ = 2` is dominated by the existing `epsMCA`.
The two per-`u` bad events in fact coincide, so the supremum is bounded. -/

/-- With `exp = id` and `parℓ = 2`, the power-generator curve is the affine line. -/
theorem curveComb_two_eq (u : WordStack A (Fin 2) ι) (γ : F) :
    curveComb (ι := ι) (A := A) (fun j : Fin 2 => (j : ℕ)) u γ = u 0 + γ • u 1 := by
  funext i
  simp only [curveComb, Fin.sum_univ_two]
  -- `γ^(0) • u 0 i + γ^(1) • u 1 i = u 0 i + γ • u 1 i`
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]
  rfl

/-- **`Fin 2` specialization of `pairJointAgreesOnP`.** For a two-row stack `u`, the
`parℓ`-ary joint-agreement predicate is equivalent to the existing two-word
`ProximityGap.pairJointAgreesOn C S (u 0) (u 1)`. -/
theorem pairJointAgreesOnP_two_iff (C : Set (ι → A)) (S : Finset ι)
    (u : WordStack A (Fin 2) ι) :
    pairJointAgreesOnP C S u ↔ ProximityGap.pairJointAgreesOn C S (u 0) (u 1) := by
  rw [pairJointAgreesOnP_iff_stackJointAgreesOn]
  exact ProximityGap.stackJointAgreesOn_pair_iff C S u

/-- At two rows, the canonical-exponent `mcaEventP` is the affine-line MCA event. -/
theorem mcaEventP_two_iff_mcaEvent (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F) :
    mcaEventP C (fun j : Fin 2 => (j : ℕ)) δ u γ ↔
      ProximityGap.mcaEvent C δ (u 0) (u 1) γ := by
  rw [mcaEventP_val_iff_mcaEventCurve]
  exact ProximityGap.mcaEventCurve_pair_iff C δ u γ

/-- Forward event bridge from `mcaEventP` to affine-line `mcaEvent`. -/
theorem mcaEventP_two_imp_mcaEvent (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F)
    (h : mcaEventP C (fun j : Fin 2 => (j : ℕ)) δ u γ) :
    ProximityGap.mcaEvent C δ (u 0) (u 1) γ :=
  (mcaEventP_two_iff_mcaEvent C δ u γ).mp h

/-- Reverse event bridge from affine-line `mcaEvent` to canonical two-row `mcaEventP`. -/
theorem mcaEvent_imp_mcaEventP_two (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) (γ : F)
    (h : ProximityGap.mcaEvent C δ (u 0) (u 1) γ) :
    mcaEventP C (fun j : Fin 2 => (j : ℕ)) δ u γ :=
  (mcaEventP_two_iff_mcaEvent C δ u γ).mpr h

/-- **Bridge lemma (`Fin 2`).** With the canonical RS exponent `exp j = (j : ℕ)`, the
general-`parℓ` MCA error at `parℓ = 2` is bounded by the existing affine-line
`ProximityGap.epsMCA`. The per-`u` bad events coincide
(`mcaEventP C id δ u γ ↔ ProximityGap.mcaEvent C δ (u 0) (u 1) γ`), so the suprema match up
to `≤`. This directly relates the general layer back to the `Fin 2` ceiling. -/
theorem epsMCAP_two_le_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAP (F := F) C (fun j : Fin 2 => (j : ℕ)) δ ≤ ProximityGap.epsMCA (F := F) C δ := by
  classical
  unfold epsMCAP ProximityGap.epsMCA
  apply iSup_mono
  intro u
  apply Pr_le_Pr_of_implies
  intro γ h_event
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, hpair⟩ := h_event
  refine ⟨S, hS_card, ⟨w, hw_mem, ?_⟩, ?_⟩
  · intro i hi
    rw [hw_eq i hi]
    exact congrFun (curveComb_two_eq u γ) i
  · -- `¬ pairJointAgreesOn` from `¬ pairJointAgreesOnP` via the two-row equivalence.
    intro hpa
    exact hpair ((pairJointAgreesOnP_two_iff C S u).mpr hpa)

open Classical in
/-- Reverse inequality for the `Fin 2` specialization. Together with the older
`epsMCAP_two_le_epsMCA`, this upgrades the bridge to equality. -/
theorem epsMCA_le_epsMCAP_two (C : Set (ι → A)) (δ : ℝ≥0) :
    ProximityGap.epsMCA (F := F) C δ ≤
      epsMCAP (F := F) C (fun j : Fin 2 => (j : ℕ)) δ := by
  unfold ProximityGap.epsMCA epsMCAP
  apply iSup_mono
  intro u
  exact Pr_le_Pr_of_implies _ _ _ fun γ h =>
    mcaEvent_imp_mcaEventP_two C δ u γ h

/-- **Exact `Fin 2` bridge.** The general power-generator MCA error at the canonical
two-row exponent is exactly the affine-line `epsMCA`. -/
theorem epsMCAP_two_eq_epsMCA (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCAP (F := F) C (fun j : Fin 2 => (j : ℕ)) δ =
      ProximityGap.epsMCA (F := F) C δ :=
  le_antisymm (epsMCAP_two_le_epsMCA C δ) (epsMCA_le_epsMCAP_two C δ)

/-- The two-row monotonicity theorem is a specialization of the arbitrary-exponent
`epsMCAP_mono`, hence also of the curve-MCA monotonicity bridge. -/
theorem epsMCA_mono_via_epsMCAP (C : Set (ι → A)) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    ProximityGap.epsMCA (F := F) C δ ≤ ProximityGap.epsMCA (F := F) C δ' := by
  rw [← epsMCAP_two_eq_epsMCA (F := F) C δ, ← epsMCAP_two_eq_epsMCA (F := F) C δ']
  exact epsMCAP_mono C (fun j : Fin 2 => (j : ℕ)) h

/-! ## WHIR `proximityCondition` (general `parℓ`) bound by `epsMCAP`

The general-`parℓ` analogue of `MutualCorrAgreement.Pr_proximityCondition_le_epsMCA`. We
instantiate the WHIR `proximityCondition` (already stated for general `parℓ`) at the
power-generator `r = fun j ↦ γ^(exp j)` and dominate it by `epsMCAP`. The structure mirrors
`MutualCorrAgreement.proximityCondition_imp_mcaEvent_affineLine`: a nonempty witness `S`
gives an unmatched row `i`, which forces the joint-disagreement clause. -/

variable {parℓ : ℕ}

/-- **Predicate bridge: WHIR `proximityCondition` (general `parℓ`, power generator) ⟹
`mcaEventP`.** When the generator scalars are `r j = γ^(exp j)` (the RS power generator),
the WHIR per-row event implies the `parℓ`-ary MCA event. The per-row unmatched index `i`
from `proximityCondition` (its clause iii) supplies the joint-disagreement clause: a row
that no single codeword matches on `S` certainly cannot be part of a *joint* codeword tuple
agreeing on `S`.

The `δ < 1` hypothesis (with `n > 0`) guarantees `S` is nonempty, so the per-row clause —
which is quantified inside `∀ s ∈ S` in `proximityCondition` — actually fires. -/
theorem proximityConditionP_imp_mcaEventP
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (exp : Fin parℓ → ℕ) (f : Fin parℓ → ι → F) (γ : F)
    (h : MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ
        (fun j => γ ^ (exp j)) C) :
    mcaEventP (F := F) (A := F) (C : Set (ι → F)) exp δ f γ := by
  classical
  obtain ⟨S, hS_card, u, hu_mem, h_inner⟩ := h
  -- `S` is nonempty since `S.card ≥ (1-δ)·n > 0`.
  have hn_pos : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h_pos : (0 : ℝ≥0) < (1 - δ) * Fintype.card ι :=
    mul_pos (tsub_pos_of_lt hδ) hn_pos
  have hS_nonempty : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hempty | hne
    · subst hempty
      simp only [Finset.card_empty, Nat.cast_zero] at hS_card
      exact absurd hS_card (not_le.mpr h_pos)
    · exact hne
  obtain ⟨s₀, hs₀⟩ := hS_nonempty
  obtain ⟨_, i, h_unmatched⟩ := h_inner s₀ hs₀
  refine ⟨S, hS_card, ⟨u, hu_mem, ?_⟩, ?_⟩
  · -- curve agreement: `u s = ∑ⱼ γ^(exp j) * f j s = ∑ⱼ γ^(exp j) • f j s = curveComb …`.
    intro s hs
    obtain ⟨hu_eq, _⟩ := h_inner s hs
    rw [hu_eq]
    simp only [curveComb, smul_eq_mul]
  · -- joint disagreement: row `i` is unmatched by any single codeword, so no joint tuple.
    rintro ⟨v, hv_mem, hv_agree⟩
    obtain ⟨s, hs, hne⟩ := h_unmatched (v i) (hv_mem i)
    exact hne (hv_agree s hs i)

/-- **General-`parℓ` analogue of `MutualCorrAgreement.Pr_proximityCondition_le_epsMCA`.**
For any word stack `f : Fin parℓ → ι → F`, the probability over `γ ←$ᵖ F` of WHIR's
`proximityCondition` with the RS power generator `r = fun j ↦ γ^(exp j)` is bounded by the
general-`parℓ` MCA error `epsMCAP C exp δ`. This lets downstream WHIR proofs cite an MCA
bound at *general* `parℓ` (the `genRSC` regime), not only the affine-line `Fin 2` case. -/
theorem Pr_proximityConditionP_le_epsMCAP
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (exp : Fin parℓ → ℕ) (f : Fin parℓ → ι → F) :
    Pr_{let γ ← $ᵖ F}[MutualCorrAgreement.proximityCondition (parℓ := Fin parℓ) f δ
        (fun j => γ ^ (exp j)) C]
      ≤ epsMCAP (F := F) (A := F) (C : Set (ι → F)) exp δ := by
  classical
  refine le_trans ?_ (le_iSup
    (fun u : WordStack F (Fin parℓ) ι ↦
      Pr_{let γ ← $ᵖ F}[mcaEventP (F := F) (A := F) (C : Set (ι → F)) exp δ u γ]) f)
  exact Pr_le_Pr_of_implies _ _ _
    (fun γ h ↦ proximityConditionP_imp_mcaEventP hδ exp f γ h)

end

end ProximityGapP
