/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# R390: per-frequency-shadow — the reverse arrow: sup bound ⟹ DC energy residual (#466)

Session 2026-07-09, issue #466, route `per-frequency-shadow`.  Companion to this session's
r341 exact Mellin/coset dictionary (`_R341CAZACCosetEquivalence.lean`, commit 681128736) and
to `_R376PerFrequencyShadowLogMEndpoint.lean`, which landed the FORWARD arrow of the route
(depth-`⌈log m⌉` residual ⟹ `WorstCaseIncompleteSumBound` at `2e·K·n·(log(m+1)+1)`) plus the
unconditional coset floor `n·‖η_{b₀}‖^{2r} ≤ q·E_r − n^{2r}`.  R376 deliberately left the
REVERSE arrow unformalized.  This brick supplies it, completing the machine-checked
"certified reformulation — no free lunch in either direction" status of the route.

## Dictionary (paper → Lean)

With `q = Fintype.card F`, `G ⊆ F` a finite subset (`n = G.card`; NO subgroup structure is
needed anywhere in this file — everything below holds for an arbitrary `Finset F`),
`η_b = eta ψ G b`, `E_r = rEnergy G r`, and the DC-subtracted depth-`r` gap
`dcGap_r := q·E_r − n^{2r} = Σ_{b≠0}‖η_b‖^{2r}` (the exact identity is the in-tree
`DCSubtractedMoment.sum_nonzero_moment`):

* `WorstCaseIncompleteSumBound ψ G M` (imported, `InteriorWorstCaseIncompleteSum.lean`) is
  the named open sup-norm Prop `∀ b ≠ 0, ‖η_b‖² ≤ M`;
* `DCEnergyBoundWithConstant G r K` (restated VERBATIM from
  `Frontier/_R240GeneralRFoldVariance.lean`, as in R376 — frontier files must not import
  frontier files; a consumer importing both welds the statements by `Iff.rfl`) is the
  DC-subtracted depth-`r` Wick residual `q·E_r − n^{2r} ≤ q·K^r·(2r−1)!!·n^r`.

## PROVEN here (machine-checked, axiom-clean, all UNCONDITIONAL)

* `worstCase_nonneg` — any sup-norm scale `M` is nonnegative (fields are nontrivial).
* `dcGap_le_of_worstCase` — **the upper sandwich edge**: `WorstCaseIncompleteSumBound ψ G M`
  gives `q·E_r − n^{2r} ≤ (q−1)·M^r` at EVERY depth `r`.  Together with R376's floor
  `n·‖η_{b₀}‖^{2r} ≤ q·E_r − n^{2r}` (subgroup granularity) the DC gap is now sandwiched on
  BOTH sides by the sup norm: `n·sup^{2r} ≤ dcGap_r ≤ (q−1)·sup^{2r}`.
* `dcGap_le_cosetCount_mul_of_worstCase` — the coset-count form: when `q = n·m + 1` the
  upper edge reads `dcGap_r ≤ n·m·M^r`, so the sandwich width is EXACTLY the coset count
  `m = (q−1)/n` — the factor that depth `k₀ = ⌈log m⌉` collapses to `√e` in sup coordinates
  (R376's forward endpoint).
* `dcEnergyBoundWithConstant_of_worstCase` — **the reverse arrow**: the sup bound at scale
  `M` implies the DC energy residual `DCEnergyBoundWithConstant G r (M/n)` at EVERY depth
  `r` with the matched constant `K = M/n`.  The moment residual consumed by the route is
  therefore never STRONGER than the sup bound it produces.
* `dcEnergyWallWithConstant_of_worstCase` — all-depth corollary: one sup bound discharges
  the ENTIRE constant-`K` wall `∀ r, DCEnergyBoundWithConstant G r (M/n)` simultaneously.
* `exists_eta_sq_gt_of_not_dcEnergyBoundWithConstant` — refuter direction: failure of the
  residual at ANY single depth with constant `M/n` produces an explicit per-frequency
  witness `b ≠ 0` with `‖η_b‖² > M`.  To refute the sup bound it suffices to refute the
  matched energy residual.

Composition with R376 (consumer-side weld, `Iff.rfl` on the restated def): the round trip
`WorstCaseIncompleteSumBound M ⟹ DCEnergyWall (M/n) ⟹ (depth ⌈log(m+1)⌉) ⟹
WorstCaseIncompleteSumBound (2e·M·(log(m+1)+1))` loses exactly the factor `2e·(log m + 1)` —
the two named faces of the route are equivalent up to the operative log factor, in both
directions, with all arrows machine-checked.  The sharper constant-`e` sandwich in
`κ/R²` coordinates (`R² ≥ κ_eff/e`, verifier-corrected from the earlier factor-2 claim) is a
paper computation and is NOT formalized here.

## NAMED OPEN (do not discharge)

* `WorstCaseIncompleteSumBound ψ G M` at prize scale `M = C·n·log q` (or the stronger
  `C·n·log m`) — OPEN; this file proves arrows into/out of it, not the Prop itself.
* `DCEnergyBoundWithConstant G k₀ K` at `k₀ = ⌈log(m+1)⌉`, `K = O(1)` — OPEN; by this
  file's reverse arrow plus R376's forward arrow it is the prize wall in energy
  coordinates, faithfully in both directions.  The honest open window
  `(log p)^{1+ε} ≤ m ≤ p/(log p)^{1+ε}` (r341) is unchanged: this brick re-coordinates the
  wall, it does not move it.

Everything below is proved; no `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.R390ShadowEnergyConverse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Constant-`K` DC-subtracted depth-`r` Wick target
`q·E_r − n^{2r} ≤ q·K^r·(2r−1)!!·n^r` — the named OPEN residual, restated verbatim from
`Frontier/_R240GeneralRFoldVariance.lean` (`R240GeneralRFoldVariance.DCEnergyBoundWithConstant`;
definitionally identical, weld by `Iff.rfl` in any consumer importing both files; the same
restatement convention as `_R376PerFrequencyShadowLogMEndpoint.lean`).  Do not discharge. -/
def DCEnergyBoundWithConstant (G : Finset F) (r : ℕ) (K : ℝ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ)
        * (K ^ r * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))

/-- All-rung constant-`K` DC-subtracted Wick wall, restated verbatim from
`Frontier/_R240GeneralRFoldVariance.lean` (weld by `Iff.rfl`). -/
def DCEnergyWallWithConstant (G : Finset F) (K : ℝ) : Prop :=
  ∀ r : ℕ, DCEnergyBoundWithConstant G r K

/-- Any scale witnessing the sup-norm Prop is nonnegative: `‖η_1‖² ≥ 0` and `1 ≠ 0` in a
field. -/
theorem worstCase_nonneg {ψ : AddChar F ℂ} {G : Finset F} {M : ℝ}
    (hwc : WorstCaseIncompleteSumBound ψ G M) : 0 ≤ M :=
  le_trans (sq_nonneg ‖eta ψ G 1‖) (hwc 1 one_ne_zero)

/-- **The upper sandwich edge.**  The sup-norm bound at scale `M` caps the DC-subtracted
depth-`r` moment at every depth: `q·E_r − n^{2r} ≤ (q−1)·M^r`.  Dual to the (subgroup-
granularity) floor `n·‖η_{b₀}‖^{2r} ≤ q·E_r − n^{2r}` of
`_R376PerFrequencyShadowLogMEndpoint.lean`; no subgroup structure is needed on this side. -/
theorem dcGap_le_of_worstCase
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {M : ℝ}
    (hwc : WorstCaseIncompleteSumBound ψ G M) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ r := by
  classical
  rw [← sum_nonzero_moment hψ G r]
  have hterm : ∀ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) ≤ M ^ r := by
    intro b hb
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    calc ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by rw [pow_mul]
      _ ≤ M ^ r := pow_le_pow_left₀ (sq_nonneg _) (hwc b hb0) r
  have hsum := Finset.sum_le_card_nsmul (Finset.univ.erase (0 : F))
    (fun b => ‖eta ψ G b‖ ^ (2 * r)) (M ^ r) hterm
  rw [nsmul_eq_mul] at hsum
  have hcard : (((Finset.univ.erase (0 : F)).card : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  rw [hcard] at hsum
  exact hsum

/-- **Coset-count form of the upper edge.**  When `G` has exactly `m` cosets
(`q = n·m + 1`), the edge reads `q·E_r − n^{2r} ≤ n·m·M^r`.  Against R376's floor
`n·sup^{2r} ≤ q·E_r − n^{2r}` the sandwich width is EXACTLY the coset count `m` — the factor
that the depth-`⌈log m⌉` endpoint collapses to `√e` in sup coordinates. -/
theorem dcGap_le_cosetCount_mul_of_worstCase
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {M : ℝ} {m : ℕ}
    (hcount : Fintype.card F = G.card * m + 1)
    (hwc : WorstCaseIncompleteSumBound ψ G M) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ (G.card : ℝ) * (m : ℝ) * M ^ r := by
  have h := dcGap_le_of_worstCase hψ hwc r
  have hq : (Fintype.card F : ℝ) - 1 = (G.card : ℝ) * (m : ℝ) := by
    have hcast : (Fintype.card F : ℝ) = (G.card : ℝ) * (m : ℝ) + 1 := by
      exact_mod_cast hcount
    linarith
  rwa [hq] at h

/-- **The reverse arrow (the certified-reformulation direction).**  The sup-norm bound at
scale `M` implies the DC energy residual at EVERY depth `r`, with the matched constant
`K = M/n`: the depth-`r` moment hypothesis consumed by the per-frequency-shadow route is
never stronger than the sup bound it is meant to produce.  Chain:
`q·E_r − n^{2r} ≤ (q−1)·M^r ≤ q·M^r = q·(M/n)^r·n^r ≤ q·(M/n)^r·(2r−1)!!·n^r`. -/
theorem dcEnergyBoundWithConstant_of_worstCase
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} (hne : G.Nonempty) {M : ℝ}
    (hwc : WorstCaseIncompleteSumBound ψ G M) (r : ℕ) :
    DCEnergyBoundWithConstant G r (M / (G.card : ℝ)) := by
  have hn : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hM0 : (0 : ℝ) ≤ M := worstCase_nonneg hwc
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hd1 : (1 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
    have h : 1 ≤ Nat.doubleFactorial (2 * r - 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
    exact_mod_cast h
  have hgap := dcGap_le_of_worstCase hψ hwc r
  unfold DCEnergyBoundWithConstant
  have hMr : (M / (G.card : ℝ)) ^ r * (G.card : ℝ) ^ r = M ^ r := by
    rw [← mul_pow, div_mul_cancel₀ M (ne_of_gt hn)]
  have hMrn : (0 : ℝ) ≤ M ^ r := pow_nonneg hM0 r
  have hstep : ((Fintype.card F : ℝ) - 1) * M ^ r
      ≤ (Fintype.card F : ℝ)
          * ((M / (G.card : ℝ)) ^ r
              * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) := by
    have hKr : (0 : ℝ) ≤ (M / (G.card : ℝ)) ^ r := by positivity
    have hnr : (0 : ℝ) ≤ (G.card : ℝ) ^ r := by positivity
    have hinner : (M / (G.card : ℝ)) ^ r * (G.card : ℝ) ^ r
        ≤ (M / (G.card : ℝ)) ^ r
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnr hd1) hKr
    calc ((Fintype.card F : ℝ) - 1) * M ^ r
        ≤ (Fintype.card F : ℝ) * M ^ r := by nlinarith
      _ = (Fintype.card F : ℝ) * ((M / (G.card : ℝ)) ^ r * (G.card : ℝ) ^ r) := by
          rw [hMr]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner hq0
  exact hgap.trans hstep

/-- **All-depth corollary.**  One sup-norm bound discharges the ENTIRE constant-`K` wall at
the matched constant `K = M/n`, all depths simultaneously — the wall Prop is, as a family,
no stronger than the single sup bound. -/
theorem dcEnergyWallWithConstant_of_worstCase
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} (hne : G.Nonempty) {M : ℝ}
    (hwc : WorstCaseIncompleteSumBound ψ G M) :
    DCEnergyWallWithConstant G (M / (G.card : ℝ)) :=
  fun r => dcEnergyBoundWithConstant_of_worstCase hψ hne hwc r

/-- **Refuter direction.**  Failure of the DC energy residual at ANY single depth `r` with
the matched constant `M/n` produces an explicit per-frequency witness above scale `M`:
to refute the sup-norm bound it suffices to refute the matched moment residual. -/
theorem exists_eta_sq_gt_of_not_dcEnergyBoundWithConstant
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} (hne : G.Nonempty) {M : ℝ} {r : ℕ}
    (hnot : ¬ DCEnergyBoundWithConstant G r (M / (G.card : ℝ))) :
    ∃ b : F, b ≠ 0 ∧ M < ‖eta ψ G b‖ ^ 2 := by
  by_contra hcon
  push_neg at hcon
  exact hnot (dcEnergyBoundWithConstant_of_worstCase hψ hne (fun b hb => hcon b hb) r)

end ArkLib.ProximityGap.R390ShadowEnergyConverse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.worstCase_nonneg
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.dcGap_le_of_worstCase
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.dcGap_le_cosetCount_mul_of_worstCase
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.dcEnergyBoundWithConstant_of_worstCase
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.dcEnergyWallWithConstant_of_worstCase
#print axioms ArkLib.ProximityGap.R390ShadowEnergyConverse.exists_eta_sq_gt_of_not_dcEnergyBoundWithConstant
