/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleSingleDefectDeficit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Single-defect QUANTITATIVE deficit: the FIRST-POWER drop, lower-bounded explicitly

**Door (iv), Lane 2/3 — frontier-movement, extends `_JacobiCocycleSingleDefectDeficit`.**

`_JacobiCocycleSingleDefectDeficit` proved the strict drop `‖∑ γ‖ < M` (qualitative) and, in
`single_defect_normSq_eq`, the exact SQUARED deficit `normSq(∑ γ) = M² − 2(M−1)(1 − Re w)`. What was
still missing is a bound on the FIRST-POWER deficit `M − ‖∑ γ‖` itself (the squared identity does not,
on its own, give a linear-in-defect floor on `M − ‖∑ γ‖`, because the square root is concave).

This file supplies exactly that rung. Using the concavity chord `√(M² − t) ≤ M − t/(2M)` on the
squared identity (`t = 2(M−1)(1 − Re w)`):

  **deficit  `M − ‖∑ γ‖ ≥ (M − 1)·(1 − Re w) / M`.**

The bound is tight as `w → 1` (probe `probe_dooriv_singledefect_quant_deficit.py`: min ratio 1.0).
It is the first-power companion to the already-landed squared identity, and the quantitative
strengthening of the qualitative strict drop.

## HONEST SCOPE
This quantifies the FIRST-POWER deficit at the MINIMAL (single) defect only, in terms of that one
phase's real-part defect. It does NOT lower-bound the FULL dispersion at the `√(n log m)` prize scale
(many-defect, adversarially-phased) — that remains the open `JacobiCocycleDispersion`, untouched. The
single-defect linear-in-`d` floor cannot by itself reach the prize scale. NO CORE / cancellation /
completion / anti-concentration / moment-saving / capacity claim. Prize CORE stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
open ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit

/-- **Concavity chord: `√(M² − t) ≤ M − t/(2M)`** for `0 < M` and `0 ≤ t ≤ M²`. The tangent/chord
inequality that converts the quadratic (squared) deficit into an explicit linear-in-`t` first-power
floor. -/
theorem sqrt_sub_le_linear {M t : ℝ} (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ M ^ 2) :
    Real.sqrt (M ^ 2 - t) ≤ M - t / (2 * M) := by
  have hrhs_nonneg : 0 ≤ M - t / (2 * M) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith [htM]
  have hsq : M ^ 2 - t ≤ (M - t / (2 * M)) ^ 2 := by
    have hexp : (M - t / (2 * M)) ^ 2 = M ^ 2 - t + t ^ 2 / (4 * M ^ 2) := by
      field_simp; ring
    rw [hexp]
    have : 0 ≤ t ^ 2 / (4 * M ^ 2) := by positivity
    linarith
  calc Real.sqrt (M ^ 2 - t)
      ≤ Real.sqrt ((M - t / (2 * M)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = M - t / (2 * M) := Real.sqrt_sq hrhs_nonneg

/-- **Reusable squared-deficit → first-power-deficit bridge.** If a complex phase sum has squared norm
at most `M² − t`, then its FIRST-POWER deficit from the triangle ceiling `M` is at least `t/(2M)`. This
is the normalized chord-conversion form used by the single-defect theorem below, and it is the generic
Door-IV audit API for any proposed mechanism that first proves a squared deficit. -/
theorem deficit_ge_of_normSq_le {M t : ℝ} {z : ℂ} (hM : 0 < M) (ht0 : 0 ≤ t)
    (htM : t ≤ M ^ 2) (hz : Complex.normSq z ≤ M ^ 2 - t) :
    t / (2 * M) ≤ M - ‖z‖ := by
  have hnorm : ‖z‖ = Real.sqrt (Complex.normSq z) := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hsqrt_le : Real.sqrt (Complex.normSq z) ≤ Real.sqrt (M ^ 2 - t) :=
    Real.sqrt_le_sqrt hz
  have hlinear : Real.sqrt (M ^ 2 - t) ≤ M - t / (2 * M) :=
    sqrt_sub_le_linear hM ht0 htM
  rw [hnorm]
  linarith

/-- **Strict form of the squared-deficit bridge.** A positive squared deficit below the ceiling forces a
strict first-power drop below `M`. This packages the audit use case: any nonzero certified squared saving is
already enough to rule out exact triangle saturation, but only with the quantitative loss exposed by
`deficit_ge_of_normSq_le`. -/
theorem norm_lt_of_pos_normSq_deficit {M t : ℝ} {z : ℂ} (hM : 0 < M) (ht0 : 0 < t)
    (htM : t ≤ M ^ 2) (hz : Complex.normSq z ≤ M ^ 2 - t) :
    ‖z‖ < M := by
  have hdef : t / (2 * M) ≤ M - ‖z‖ :=
    deficit_ge_of_normSq_le hM (le_of_lt ht0) htM hz
  have hpos : 0 < t / (2 * M) := by positivity
  linarith

/-- **Exact first-power closed form for a single defect.** The squared-deficit identity from
`_JacobiCocycleSingleDefectDeficit` becomes an exact norm formula after taking the nonnegative square
root. This exposes the precise first-power object before the chord lower bound below discards information. -/
theorem single_defect_norm_eq_sqrt {M : ℕ} (hM : 1 ≤ M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    ‖phaseSum γ‖ =
      Real.sqrt ((M : ℝ) ^ 2 - 2 * ((M : ℝ) - 1) * (1 - w.re)) := by
  have hnorm : ‖phaseSum γ‖ = Real.sqrt (Complex.normSq (phaseSum γ)) := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, single_defect_normSq_eq hM i₀ w hw γ hi hrest]

/-- **Quantitative single-defect deficit (the explicit first-power drop).** Under the single-defect
hypotheses (`γ ≡ 1` off one index `i₀`, `γ i₀ = w` unit, `w ≠ 1`, `M > 1`), the FIRST-POWER deficit
is at least `(M − 1)(1 − Re w)/M`:

  `M − ‖phaseSum γ‖ ≥ (M − 1)(1 − Re w)/M > 0`.

Built on the already-landed squared identity `single_defect_normSq_eq` plus the concavity chord. The
strict positivity recovers `single_defect_phaseSum_lt`; the explicit first-power floor is the new
content. -/
theorem single_defect_deficit_ge {M : ℕ} (hM : 1 < M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (hne : w ≠ 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    ((M : ℝ) - 1) * (1 - w.re) / (M : ℝ) ≤ (M : ℝ) - ‖phaseSum γ‖ := by
  have hMr : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  -- real-part defect d ∈ (0, 2]
  have hd0 : 0 < 1 - w.re := by have := unit_ne_one_re_lt_one hw hne; linarith
  have hd2 : 1 - w.re ≤ 2 := by
    have hge : -1 ≤ w.re := by
      have hns : Complex.normSq w = 1 := by
        have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
      have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
        simpa [Complex.normSq_apply, sq] using hns
      nlinarith [sq_nonneg w.im, sq_nonneg (w.re + 1)]
    linarith
  set d : ℝ := 1 - w.re with hdef
  have hdpos : 0 < d := hd0
  have hdle : d ≤ 2 := hd2
  set t : ℝ := 2 * ((M : ℝ) - 1) * d with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; nlinarith [hMr, hdpos]
  have htM : t ≤ (M : ℝ) ^ 2 := by
    rw [htdef]; nlinarith [hMr, hdle, hdpos, sq_nonneg ((M : ℝ) - 2)]
  -- squared deficit identity (already landed)
  have hnormsq : Complex.normSq (phaseSum γ) = (M : ℝ) ^ 2 - t := by
    rw [single_defect_normSq_eq (by omega : 1 ≤ M) i₀ w hw γ hi hrest, htdef]
  have hnorm : ‖phaseSum γ‖ = Real.sqrt ((M : ℝ) ^ 2 - t) := by
    have h1 : ‖phaseSum γ‖ = Real.sqrt (Complex.normSq (phaseSum γ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [h1, hnormsq]
  -- concavity chord
  have hsqrt_le : Real.sqrt ((M : ℝ) ^ 2 - t) ≤ (M : ℝ) - t / (2 * (M : ℝ)) :=
    sqrt_sub_le_linear hM0 ht0 htM
  have hfloor : t / (2 * (M : ℝ)) = ((M : ℝ) - 1) * d / (M : ℝ) := by
    rw [htdef]; field_simp
  rw [hnorm]
  have heq : ((M : ℝ) - 1) * (1 - w.re) / (M : ℝ) = t / (2 * (M : ℝ)) := hfloor.symm
  rw [heq]
  linarith [hsqrt_le]

end ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit.sqrt_sub_le_linear
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit.deficit_ge_of_normSq_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit.norm_lt_of_pos_normSq_deficit
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit.single_defect_norm_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit.single_defect_deficit_ge
