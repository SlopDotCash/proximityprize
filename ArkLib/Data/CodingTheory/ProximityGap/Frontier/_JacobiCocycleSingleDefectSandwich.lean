/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleSingleDefectQuantDeficit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Single-defect FIRST-POWER deficit sandwich

**Door (iv), Lane 3 — constraint/audit extension of the single-defect model.**

`_JacobiCocycleSingleDefectQuantDeficit` converted the exact squared identity into the lower floor

`(M - 1)(1 - Re w)/M ≤ M - ‖phaseSum γ‖`.

This file pins the complementary ceiling: the SAME one-defect first-power loss is never more than twice
that floor. Equivalently, in the exact planar model, the single-defect loss is trapped in the sharp
factor-2 window

`(M - 1)(1 - Re w)/M ≤ M - ‖phaseSum γ‖ ≤ 2(M - 1)(1 - Re w)/M`.

Probe: `scripts/probes/probe_dooriv_singledefect_sandwich.py` checked `M=2..256` over a dense unit-circle
mesh; the lower ratio tends to `1` near alignment and the upper ratio tends to `2` at the opposite phase,
so the factor-2 window is tight.

## HONEST SCOPE
This is an audit constraint for the MINIMAL one-defect Jacobi-cocycle model. It says a lone off-aligned
phase has no hidden superlinear first-power loss: its effect is exactly real-part defect up to a sharp
constant factor. It does NOT prove many-defect dispersion, anti-concentration, CORE, completion,
moment-saving, or capacity. Prize CORE remains OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectSandwich

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
open ProximityGap.Frontier.JacobiCocycleSingleDefectDeficit
open ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit

/-- **Square-root deficit ceiling.** If `0 < M` and `0 ≤ t ≤ M²`, then the first-power deficit between
`M` and `√(M²-t)` is at most `t/M`. This is the upper companion to `sqrt_sub_le_linear`, and follows from
`√(M²-t) ≤ M` plus `s² = M²-t`: `M(M-s) ≤ t` is equivalent to `s² ≤ Ms`. -/
theorem sqrt_sub_deficit_le {M t : ℝ} (hM : 0 < M) (ht0 : 0 ≤ t) (htM : t ≤ M ^ 2) :
    M - Real.sqrt (M ^ 2 - t) ≤ t / M := by
  set s : ℝ := Real.sqrt (M ^ 2 - t) with hs
  have hsub0 : 0 ≤ M ^ 2 - t := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = M ^ 2 - t := by rw [hs, Real.sq_sqrt hsub0]
  have hs_le_M : s ≤ M := by
    rw [hs]
    calc Real.sqrt (M ^ 2 - t)
        ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = M := Real.sqrt_sq (by linarith)
  apply (le_div_iff₀ hM).mpr
  nlinarith [hs_sq, hs0, hs_le_M]

/-- **Upper half of the one-defect sandwich.** Under the single-defect hypotheses, the FIRST-POWER
loss is bounded above by twice the lower floor:

`M - ‖phaseSum γ‖ ≤ 2(M - 1)(1 - Re w)/M`.

Thus a single off-aligned phase cannot hide a larger-than-real-part first-power saving. -/
theorem single_defect_deficit_le {M : ℕ} (hM : 1 < M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    (M : ℝ) - ‖phaseSum γ‖ ≤ 2 * ((M : ℝ) - 1) * (1 - w.re) / (M : ℝ) := by
  have hMr : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hd0 : 0 ≤ 1 - w.re := by
    have hns : Complex.normSq w = 1 := by
      have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
    have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, sq] using hns
    nlinarith [sq_nonneg w.im, sq_nonneg (w.re - 1)]
  have hd2 : 1 - w.re ≤ 2 := by
    have hns : Complex.normSq w = 1 := by
      have := Complex.normSq_eq_norm_sq w; rw [this, hw]; norm_num
    have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, sq] using hns
    nlinarith [sq_nonneg w.im, sq_nonneg (w.re + 1)]
  set d : ℝ := 1 - w.re with hdef
  have hdnonneg : 0 ≤ d := hd0
  have hdle : d ≤ 2 := hd2
  set t : ℝ := 2 * ((M : ℝ) - 1) * d with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; nlinarith [hMr, hdnonneg]
  have htM : t ≤ (M : ℝ) ^ 2 := by
    rw [htdef]; nlinarith [hMr, hdle, hdnonneg, sq_nonneg ((M : ℝ) - 2)]
  have hnormsq : Complex.normSq (phaseSum γ) = (M : ℝ) ^ 2 - t := by
    rw [single_defect_normSq_eq (by omega : 1 ≤ M) i₀ w hw γ hi hrest, htdef]
  have hnorm : ‖phaseSum γ‖ = Real.sqrt ((M : ℝ) ^ 2 - t) := by
    have h1 : ‖phaseSum γ‖ = Real.sqrt (Complex.normSq (phaseSum γ)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [h1, hnormsq]
  have hceil := sqrt_sub_deficit_le hM0 ht0 htM
  have hfloor : t / (M : ℝ) = 2 * ((M : ℝ) - 1) * d / (M : ℝ) := by
    rw [htdef]
  rw [hnorm]
  rw [← hfloor]
  exact hceil

/-- **Single-defect first-power sandwich.** With one unimodular defect `w ≠ 1`, the deficit is trapped
between the already-landed lower floor and the sharp factor-2 ceiling. -/
theorem single_defect_deficit_sandwich {M : ℕ} (hM : 1 < M) (i₀ : Fin M) (w : ℂ)
    (hw : ‖w‖ = 1) (hne : w ≠ 1) (γ : Fin M → ℂ)
    (hi : γ i₀ = w) (hrest : ∀ j, j ≠ i₀ → γ j = 1) :
    ((M : ℝ) - 1) * (1 - w.re) / (M : ℝ) ≤ (M : ℝ) - ‖phaseSum γ‖ ∧
      (M : ℝ) - ‖phaseSum γ‖ ≤ 2 * ((M : ℝ) - 1) * (1 - w.re) / (M : ℝ) := by
  constructor
  · exact single_defect_deficit_ge hM i₀ w hw hne γ hi hrest
  · exact single_defect_deficit_le hM i₀ w hw γ hi hrest

end ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectSandwich

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectSandwich.sqrt_sub_deficit_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectSandwich.single_defect_deficit_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleSingleDefectSandwich.single_defect_deficit_sandwich
