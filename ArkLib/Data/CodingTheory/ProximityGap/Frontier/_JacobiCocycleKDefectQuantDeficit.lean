/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleSingleDefectQuantDeficit
import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

/-!
# k-defect QUANTITATIVE deficit: additive-in-defect first-power floor

**Door (iv), Lane 2/3 — frontier-movement, generalizes the single-defect deficit to all `k`.**

`_JacobiCocycleSingleDefectQuantDeficit` floored the first-power deficit when EXACTLY ONE phase is
off-aligned. This file generalizes to ANY defect set `S` of `k` indices: if a unit-phase family `γ`
over `Fin M` equals the aligned baseline `1` off `S` and takes a unit value `γ i = w i ≠ 1` on each
`i ∈ S`, then writing the total real-part defect `D = ∑_{i∈S}(1 − Re (w i))`,

  **`M − ‖∑ γ‖ ≥ (M − k)·D / M`   (for `M ≥ k`).**

So the first-power deficit grows at least linearly in the AGGREGATE real-part defect of the off-aligned
phases — an additive-in-defect floor, the natural multi-defect bridge above the single-defect rung.

The derivation (all kernel-clean):
* `Re(∑ γ) = M − D` and `∑ γ = (M − k) + ∑_{i∈S} w i`.
* The two Cauchy–Schwarz inequalities `(∑ sin)² ≤ k·∑ sin²` and `D² ≤ k·∑ d²`, with the unit-circle
  identity `sin² = 2d − d²`, collapse to `D² + (∑ sin)² ≤ 2kD`, hence
  `normSq(∑ γ) = (M − D)² + (∑ sin)² ≤ M² − 2(M − k)D`.
* The concavity chord `√(M² − t) ≤ M − t/(2M)` (from the single-defect file) finishes it.

Probes `probe_dooriv_{twodefect,kdefect}_quant_deficit.py` + `probe_dooriv_kdefect_normsq_bound.py`
validate the floor and each rung (0 failures over `M` up to 256, `k` up to 10; tight, ratio → 1).

## HONEST SCOPE
This is an AGGREGATE first-power floor in the total real-part defect at FIXED defect cardinality. It is
NOT the `√(n log m)`-scale dispersion lower bound the prize needs: the worst adversarial coset has
EVERY phase off-aligned with `D = Θ(n)`, where `(M − k)D/M` degenerates (the `M − k` prefactor → 0 as
`k → M`), so this floor does NOT survive to the all-defect regime. Quantifying the dispersion there is
the open `JacobiCocycleDispersion`, untouched. NO CORE / cancellation / completion / anti-concentration
/ moment-saving / capacity claim. Prize CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
open ProximityGap.Frontier.JacobiCocycleSingleDefectQuantDeficit

variable {M : ℕ} (S : Finset (Fin M)) (w : Fin M → ℂ)

/-- The defect family `γ`: `w i` on the defect set `S`, baseline `1` off it. -/
noncomputable def kDefectFamily (S : Finset (Fin M)) (w : Fin M → ℂ) : Fin M → ℂ :=
  fun i => if i ∈ S then w i else 1

/-- **Resultant decomposition.** `∑ γ = (M − k) + ∑_{i∈S} w i` for the `k`-defect family. -/
theorem kDefect_phaseSum_eq (hk : S.card ≤ M) :
    phaseSum (kDefectFamily S w) =
      (((M : ℝ) - S.card : ℝ) : ℂ) + ∑ i ∈ S, w i := by
  unfold phaseSum kDefectFamily
  have hsplit : (∑ j, (if j ∈ S then w j else (1 : ℂ)))
      = (∑ j ∈ S, w j) + (∑ j ∈ univ \ S, (1 : ℂ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)
          (fun j => if j ∈ S then w j else (1 : ℂ))]
    congr 1
    · rw [Finset.filter_mem_eq_inter, univ_inter]
      exact Finset.sum_congr rfl (fun i hi => by simp [hi])
    · rw [show (univ.filter (¬ · ∈ S)) = univ \ S from by
        ext i; simp [Finset.mem_sdiff]]
      exact Finset.sum_congr rfl (fun i hi => by
        simp only [Finset.mem_sdiff] at hi; simp [hi.2])
  have hcard : (univ \ S).card = M - S.card := by
    rw [Finset.card_univ_diff, Fintype.card_fin]
  rw [hsplit, Finset.sum_const, hcard, nsmul_eq_mul, mul_one, Nat.cast_sub hk]
  push_cast; ring

/-- **Real part of the resultant.** `Re(∑ γ) = M − D` where `D = ∑_{i∈S}(1 − Re (w i))`. -/
theorem kDefect_re_eq (hk : S.card ≤ M) :
    (phaseSum (kDefectFamily S w)).re = (M : ℝ) - ∑ i ∈ S, (1 - (w i).re) := by
  rw [kDefect_phaseSum_eq S w hk]
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_sum]
  rw [Finset.sum_sub_distrib]
  have : (∑ _i ∈ S, (1 : ℝ)) = (S.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [this]
  push_cast
  ring

/-- **Imaginary part of the resultant.** `Im(∑ γ) = ∑_{i∈S} Im (w i)` (the baseline is real). -/
theorem kDefect_im_eq (hk : S.card ≤ M) :
    (phaseSum (kDefectFamily S w)).im = ∑ i ∈ S, (w i).im := by
  rw [kDefect_phaseSum_eq S w hk]
  rw [Complex.add_im, Complex.ofReal_im, Complex.im_sum]
  ring

/-- **The Cauchy–Schwarz collapse.** With `D = ∑ d_i` (`d_i = 1 − Re w_i`) and each `w_i` unimodular,
`D² + (∑ Im w_i)² ≤ 2·k·D`. Combines `(∑ Im)² ≤ k·∑ Im²`, `D² ≤ k·∑ d²`, and the unit-circle
identity `Im² = 2d − d²`. -/
theorem kDefect_cs_collapse (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    (∑ i ∈ S, (1 - (w i).re)) ^ 2 + (∑ i ∈ S, (w i).im) ^ 2
      ≤ 2 * (S.card : ℝ) * (∑ i ∈ S, (1 - (w i).re)) := by
  set d : Fin M → ℝ := fun i => 1 - (w i).re with hd
  -- unit-circle: (Im w_i)^2 = 2 d_i - d_i^2
  have hsin : ∀ i ∈ S, (w i).im ^ 2 = 2 * d i - d i ^ 2 := by
    intro i hi
    have hns : Complex.normSq (w i) = 1 := by
      have := Complex.normSq_eq_norm_sq (w i); rw [this, hunit i hi]; norm_num
    have hsq : (w i).re ^ 2 + (w i).im ^ 2 = 1 := by
      simpa [Complex.normSq_apply, sq] using hns
    simp only [hd]; nlinarith [hsq]
  -- CS1: (∑ Im)^2 ≤ k ∑ Im^2
  have hcs1 : (∑ i ∈ S, (w i).im) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, (w i).im ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => (w i).im)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, sq] using h
  -- CS2: D^2 ≤ k ∑ d^2
  have hcs2 : (∑ i ∈ S, d i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, d i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => d i)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, sq] using h
  -- ∑ Im^2 = 2D - ∑ d^2
  have hsumsin : (∑ i ∈ S, (w i).im ^ 2)
      = 2 * (∑ i ∈ S, d i) - (∑ i ∈ S, d i ^ 2) := by
    rw [Finset.sum_congr rfl hsin, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hDdef : (∑ i ∈ S, (1 - (w i).re)) = ∑ i ∈ S, d i := by rfl
  rw [hDdef]
  -- combine
  have key : (∑ i ∈ S, d i) ^ 2 + (∑ i ∈ S, (w i).im) ^ 2
      ≤ 2 * (S.card : ℝ) * (∑ i ∈ S, d i) := by
    have e1 : (∑ i ∈ S, (w i).im) ^ 2
        ≤ (S.card : ℝ) * (2 * (∑ i ∈ S, d i) - (∑ i ∈ S, d i ^ 2)) := by
      rw [← hsumsin]; exact hcs1
    nlinarith [hcs2, e1]
  exact key

/-- **Squared-deficit upper bound.** `normSq(∑ γ) ≤ M² − 2(M − k)D` with `D = ∑_{i∈S}(1−Re w_i)`,
for unit phases on the defect set and `k ≤ M`. The exact algebra: `normSq = (M−D)² + (∑ Im)²` and the
Cauchy–Schwarz collapse `D² + (∑ Im)² ≤ 2kD`. -/
theorem kDefect_normSq_le (hk : S.card ≤ M) (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    Complex.normSq (phaseSum (kDefectFamily S w))
      ≤ (M : ℝ) ^ 2 - 2 * ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) := by
  set D : ℝ := ∑ i ∈ S, (1 - (w i).re) with hDset
  have hre : (phaseSum (kDefectFamily S w)).re = (M : ℝ) - D := kDefect_re_eq S w hk
  have him : (phaseSum (kDefectFamily S w)).im = ∑ i ∈ S, (w i).im := kDefect_im_eq S w hk
  have hcs : D ^ 2 + (∑ i ∈ S, (w i).im) ^ 2 ≤ 2 * (S.card : ℝ) * D :=
    kDefect_cs_collapse S w hunit
  have hns : Complex.normSq (phaseSum (kDefectFamily S w))
      = ((M : ℝ) - D) ^ 2 + (∑ i ∈ S, (w i).im) ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  rw [hns]
  nlinarith [hcs]

/-- **k-defect total real-part defect is in `[0, 2k]`.** Each `1 − Re w_i ∈ [0,2]` for unit `w_i`. -/
theorem kDefect_D_bounds (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    0 ≤ (∑ i ∈ S, (1 - (w i).re)) ∧ (∑ i ∈ S, (1 - (w i).re)) ≤ 2 * (S.card : ℝ) := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    have : (w i).re ≤ 1 := by
      have hns : Complex.normSq (w i) = 1 := by
        have := Complex.normSq_eq_norm_sq (w i); rw [this, hunit i hi]; norm_num
      have hsq : (w i).re ^ 2 + (w i).im ^ 2 = 1 := by
        simpa [Complex.normSq_apply, sq] using hns
      nlinarith [sq_nonneg (w i).im]
    linarith
  · calc (∑ i ∈ S, (1 - (w i).re)) ≤ ∑ _i ∈ S, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have : -1 ≤ (w i).re := by
            have hns : Complex.normSq (w i) = 1 := by
              have := Complex.normSq_eq_norm_sq (w i); rw [this, hunit i hi]; norm_num
            have hsq : (w i).re ^ 2 + (w i).im ^ 2 = 1 := by
              simpa [Complex.normSq_apply, sq] using hns
            nlinarith [sq_nonneg (w i).im, sq_nonneg ((w i).re + 1)]
          linarith
      _ = 2 * (S.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **k-defect QUANTITATIVE first-power deficit floor.** For a `k`-defect unit-phase family with
`k = #S ≤ M` (and `M ≥ 1`), the first-power deficit is at least `(M − k)·D / M`, where
`D = ∑_{i∈S}(1 − Re w_i)` is the total real-part defect of the off-aligned phases:

  `M − ‖phaseSum γ‖ ≥ (M − k)·D / M`.

The additive-in-defect generalization of the single-defect floor (`k = 1` recovers it). Built on
`kDefect_normSq_le` (the Cauchy–Schwarz collapse) and the concavity chord `sqrt_sub_le_linear`. -/
theorem kDefect_deficit_ge (hM : 1 ≤ M) (hk : S.card ≤ M) (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ)
      ≤ (M : ℝ) - ‖phaseSum (kDefectFamily S w)‖ := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hkM : (S.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
  obtain ⟨hD0, hD2⟩ := kDefect_D_bounds S w hunit
  set D : ℝ := ∑ i ∈ S, (1 - (w i).re) with hDset
  set t : ℝ := 2 * ((M : ℝ) - S.card) * D with htset
  have ht0 : 0 ≤ t := by rw [htset]; nlinarith [hkM, hD0]
  have htM : t ≤ (M : ℝ) ^ 2 := by
    -- t = 2(M-k)D ≤ 4k(M-k) ≤ M^2  (AM-GM on k, M-k)
    rw [htset]
    nlinarith [hkM, hD0, hD2, sq_nonneg ((M : ℝ) - 2 * (S.card : ℝ))]
  have hnsle : Complex.normSq (phaseSum (kDefectFamily S w)) ≤ (M : ℝ) ^ 2 - t := by
    rw [htset]; exact kDefect_normSq_le S w hk hunit
  have hnormle : ‖phaseSum (kDefectFamily S w)‖ ≤ Real.sqrt ((M : ℝ) ^ 2 - t) := by
    have h1 : ‖phaseSum (kDefectFamily S w)‖
        = Real.sqrt (Complex.normSq (phaseSum (kDefectFamily S w))) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [h1]
    exact Real.sqrt_le_sqrt hnsle
  have hchord : Real.sqrt ((M : ℝ) ^ 2 - t) ≤ (M : ℝ) - t / (2 * (M : ℝ)) :=
    sqrt_sub_le_linear hM0 ht0 htM
  have hfloor : t / (2 * (M : ℝ)) = ((M : ℝ) - S.card) * D / (M : ℝ) := by
    rw [htset]; field_simp
  calc ((M : ℝ) - S.card) * D / (M : ℝ)
      = t / (2 * (M : ℝ)) := hfloor.symm
    _ ≤ (M : ℝ) - Real.sqrt ((M : ℝ) ^ 2 - t) := by linarith [hchord]
    _ ≤ (M : ℝ) - ‖phaseSum (kDefectFamily S w)‖ := by linarith [hnormle]

end ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_phaseSum_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_re_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_im_eq
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_cs_collapse
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_normSq_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_D_bounds
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefect_deficit_ge
