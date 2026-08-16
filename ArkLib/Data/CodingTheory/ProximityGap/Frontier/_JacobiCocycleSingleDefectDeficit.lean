/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DyadicJacobiCocycleNonContraction
import Mathlib.Tactic

/-!
# Single-defect strict DEFICIT: one off-aligned phase forces sub-saturation

**Door (iv), Lane 2/3 — frontier-movement, extends `_DyadicJacobiCocycleNonContraction`.**

`_JacobiCocycleAlignmentMechanism` proved the QUALITATIVE converse (sub-saturation ⟹ non-alignment).
This file proves the SHARP forward QUANTITATIVE direction at the minimal defect: if a unit-phase
configuration is the aligned baseline (`γ ≡ 1`) EXCEPT at a single index `i₀` where it takes a value
`w ≠ 1` (still unimodular), then the phase sum is STRICTLY below the saturation value `M`:
`‖∑ γ‖ < M`. So even a single off-aligned phase breaks saturation — alignment is fragile, and the
saturating worst case requires EXACT alignment of every phase.

The strict drop comes from the planar geometry: `∑ γ = (M − 1) + w`, and `‖(M−1) + w‖ < M` exactly
because `Re w < 1` for a unit `w ≠ 1` (the missing real part is the deficit). This is the sharp,
kernel-checked statement of why the trivial cocycle's saturation is unstable.

## HONEST SCOPE
This is the minimal-defect QUANTITATIVE converse (single off-aligned phase ⟹ strict deficit), the
sharp companion to the qualitative mechanism. It does NOT lower-bound the deficit at the
`√(n log m)`-scale required for the prize — quantifying the FULL dispersion is the open
`JacobiCocycleDispersion`, untouched. NO CORE / cancellation / completion / anti-concentration /
moment-saving / capacity claim. Prize CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction

/-- **Real-part deficit of a unit phase.** A unit complex number `w` with `w ≠ 1` has `Re w < 1`.
This is the geometric source of the saturation deficit. -/
theorem unit_ne_one_re_lt_one {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) : w.re < 1 := by
  have hns : Complex.normSq w = 1 := by
    have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using hns
  rcases lt_or_eq_of_le (by nlinarith [sq_nonneg w.im] : w.re ≤ 1) with h | h
  · exact h
  · exfalso
    apply hne
    have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
    apply Complex.ext <;> simp [h, him]

/-- **Exact planar deficit identity.** For a unit phase `w`, the squared norm of the one-defect
baseline `(M−1)+w` equals `M² − 2(M−1)(1−Re w)`. Thus the deficit is exactly the missing real part of the
single bad phase, with no hidden moment/completion input. -/
theorem normSq_baseline_plus_unit_eq {M : ℝ} {w : ℂ} (hw : ‖w‖ = 1) :
    Complex.normSq (((M - 1 : ℝ) : ℂ) + w) = M ^ 2 - 2 * (M - 1) * (1 - w.re) := by
  have hns : Complex.normSq w = 1 := by
    have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using hns
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im]
  nlinarith

/-- **Planar deficit bound.** For `M > 1` and a unit `w ≠ 1`, `‖(M − 1) + w‖ < M`. The missing real
part `1 − Re w > 0` of `w` keeps the resultant strictly inside the radius-`M` circle. -/
theorem norm_baseline_plus_unit_lt {M : ℝ} {w : ℂ}
    (hw : ‖w‖ = 1) (hne : w ≠ 1) (hM : 1 < M) :
    ‖((M - 1 : ℝ) : ℂ) + w‖ < M := by
  have hwre : w.re < 1 := unit_ne_one_re_lt_one hw hne
  have hns : Complex.normSq w = 1 := by
    have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using hns
  have key : Complex.normSq (((M - 1 : ℝ) : ℂ) + w) < M ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith [hsq, hwre, hM]
  have h1 : ‖((M - 1 : ℝ) : ℂ) + w‖ = Real.sqrt (Complex.normSq (((M - 1 : ℝ) : ℂ) + w)) := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h1]
  calc Real.sqrt (Complex.normSq (((M - 1 : ℝ) : ℂ) + w))
        < Real.sqrt (M ^ 2) := Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) key
    _ = M := by rw [Real.sqrt_sq (by linarith)]

/-- **Single-defect squared deficit formula.** If a unit-phase family `γ` over `Fin M` equals the aligned
baseline `1` at every index except a single `i₀` where `γ i₀ = w`, then the squared phase-sum deficit is
exactly `2(M−1)(1−Re w)`. This is the arithmetic-audit form of the single-defect mechanism: the whole loss
is the real-part defect of the lone off-aligned phase. -/
theorem single_defect_normSq_eq {M : ℕ} (hM : 1 ≤ M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    Complex.normSq (phaseSum γ) =
      (M : ℝ) ^ 2 - 2 * ((M : ℝ) - 1) * (1 - w.re) := by
  have hsplit : phaseSum γ = (∑ j ∈ univ.erase i₀, γ j) + γ i₀ := by
    unfold phaseSum
    rw [Finset.sum_erase_add _ _ (mem_univ i₀)]
  have hrestsum : (∑ j ∈ univ.erase i₀, γ j) = (((M : ℝ) - 1 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j hj => hrest j (Finset.ne_of_mem_erase hj))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub hM]
    push_cast
    ring
  rw [hsplit, hrestsum, hi]
  exact normSq_baseline_plus_unit_eq (M := (M : ℝ)) hw

/-- **Single-defect strict deficit (the sharp converse).** If a unit-phase family `γ` over `Fin M`
(`M > 1`) equals the aligned baseline `1` at every index except a single `i₀` where `γ i₀ = w` with
`‖w‖ = 1`, `w ≠ 1`, then the phase sum is STRICTLY below saturation: `‖phaseSum γ‖ < M`. One
off-aligned phase already breaks the trivial cocycle's saturation. -/
theorem single_defect_phaseSum_lt {M : ℕ} (hM : 1 < M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (hne : w ≠ 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    ‖phaseSum γ‖ < (M : ℝ) := by
  have hMr : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsplit : phaseSum γ = (∑ j ∈ univ.erase i₀, γ j) + γ i₀ := by
    unfold phaseSum
    rw [Finset.sum_erase_add _ _ (mem_univ i₀)]
  have hrestsum : (∑ j ∈ univ.erase i₀, γ j) = (((M : ℝ) - 1 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j hj => hrest j (Finset.ne_of_mem_erase hj))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega : 1 ≤ M)]
    push_cast
    ring
  rw [hsplit, hrestsum, hi]
  exact norm_baseline_plus_unit_lt hw hne hMr

end ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; no extra axioms) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit.unit_ne_one_re_lt_one
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit.normSq_baseline_plus_unit_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit.norm_baseline_plus_unit_lt
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit.single_defect_normSq_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit.single_defect_phaseSum_lt
