/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FullTowerCollapse

/-!
# LANE B2 (#466 round 28): the full-tower triangle baseline

Round 27 identifies every rung with the `L²` energy of `iterConv J r`.  This brick records the
pure triangle-inequality baseline at every depth:

* if `‖J_j‖ ≤ B` for every `j`, then `‖J^{∗r}(c)‖ ≤ m^r B^r`;
* consequently `∑_c ‖J^{∗r}(c)‖² ≤ m^(2r+1) B^(2r)`;
* with the Jacobi-size input `B² ≤ q`, the formal no-cancellation energy is
  `≤ m^(2r+1) q^r`.

Compared with the Wick target in `_R27FullTowerCollapse`,
`O(C^r r! (m q)^r)`, the baseline has the explicit extra factor `m^(r+1)` (up to the
`C^r r!` budget).  This gives the all-depth version of the R23/R26 `m²` loss: the remaining
problem is exactly the cancellation that lowers `m^(2r+1)` to Wick scale.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 28, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R28IterConvBaseline

open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

variable {m : ℕ} [NeZero m]

/-- **Pointwise triangle baseline for every iterated convolution depth.** -/
theorem norm_iterConv_le_card_pow_mul_bound (J : ZMod m → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) :
    ∀ r : ℕ, ∀ c : ZMod m, ‖iterConv J r c‖ ≤ (m : ℝ) ^ r * B ^ r := by
  intro r
  induction r with
  | zero =>
      intro c
      by_cases hc : c = 0
      · simp [iterConv, hc]
      · simp [iterConv, hc]
  | succ r ih =>
      intro c
      calc ‖iterConv J (r + 1) c‖
          ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖iterConv J r (c - j) * J j‖ := by
            simp only [iterConv]
            exact norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.univ \ {(0 : ZMod m)}, (m : ℝ) ^ r * B ^ r * B := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [norm_mul]
            exact mul_le_mul (ih (c - j)) (hJ j) (norm_nonneg _) (by positivity)
        _ = ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) * ((m : ℝ) ^ r * B ^ r * B) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ℝ) * ((m : ℝ) ^ r * B ^ r * B) := by
            have hcard : (((Finset.univ \ {(0 : ZMod m)}).card : ℝ) ≤ (m : ℝ)) := by
              have hle : (Finset.univ \ {(0 : ZMod m)}).card
                  ≤ (Finset.univ : Finset (ZMod m)).card :=
                Finset.card_le_card (by
                  intro j _hj
                  exact Finset.mem_univ j)
              simpa [ZMod.card] using (Nat.cast_le.mpr hle : _)
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (m : ℝ) ^ (r + 1) * B ^ (r + 1) := by ring

/-- **Energy triangle baseline for every depth.** -/
theorem iterConv_energy_le_card_pow_mul_bound (J : ZMod m → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) (r : ℕ) :
    ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2 ≤ (m : ℝ) ^ (2 * r + 1) * B ^ (2 * r) := by
  classical
  have hpt : ∀ c : ZMod m, ‖iterConv J r c‖ ^ 2
      ≤ ((m : ℝ) ^ r * B ^ r) ^ 2 := by
    intro c
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_iterConv_le_card_pow_mul_bound J hB0 hJ r c) 2
  calc ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2
      ≤ ∑ _c : ZMod m, ((m : ℝ) ^ r * B ^ r) ^ 2 := Finset.sum_le_sum (fun c _ => hpt c)
    _ = ((Finset.univ : Finset (ZMod m)).card : ℝ) * ((m : ℝ) ^ r * B ^ r) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) ^ (2 * r + 1) * B ^ (2 * r) := by
        simp [ZMod.card]
        ring

/-- **Jacobi-size no-cancellation baseline.**  If `‖J_j‖² ≤ q`, then the full-tower energy
is bounded by `m^(2r+1) q^r`. -/
theorem iterConv_energy_le_card_pow_mul_of_uniform_sq_bound (J : ZMod m → ℂ) (q r : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) :
    ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2 ≤ (m : ℝ) ^ (2 * r + 1) * (q : ℝ) ^ r := by
  classical
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ j : ZMod m, ‖J j‖ ≤ Real.sqrt (q : ℝ) := by
    intro j
    have h := Real.sqrt_le_sqrt (hJ j)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hbase := iterConv_energy_le_card_pow_mul_bound J hB0 hJroot r
  have hsqrt : (Real.sqrt (q : ℝ)) ^ (2 * r) = (q : ℝ) ^ r := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ (2 * r)
        = ((Real.sqrt (q : ℝ)) ^ 2) ^ r := by rw [← pow_mul]
      _ = (q : ℝ) ^ r := by rw [hs2]
  calc ∑ c : ZMod m, ‖iterConv J r c‖ ^ 2
      ≤ (m : ℝ) ^ (2 * r + 1) * (Real.sqrt (q : ℝ)) ^ (2 * r) := hbase
    _ = (m : ℝ) ^ (2 * r + 1) * (q : ℝ) ^ r := by rw [hsqrt]

end ArkLib.ProximityGap.Frontier.R28IterConvBaseline

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R28IterConvBaseline in
#print axioms
  norm_iterConv_le_card_pow_mul_bound
open ArkLib.ProximityGap.Frontier.R28IterConvBaseline in
#print axioms
  iterConv_energy_le_card_pow_mul_bound
open ArkLib.ProximityGap.Frontier.R28IterConvBaseline in
#print axioms
  iterConv_energy_le_card_pow_mul_of_uniform_sq_bound
