/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Explicit sixth-moment density from logarithmic prime mass

The two inputs are the weighted cyclotomic bound on exceptional split primes
and Lee's prime number theorem in arithmetic progressions. This module checks
the numerical and finite-set deductions for the length two to the thirtieth.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SplitPrimeSixthDensity

open Finset Real
noncomputable section

def weight (P : Finset ℕ) : ℝ := ∑ p ∈ P, Real.log (p : ℝ)

/-- The sixth-moment norm budget divided by the minimum cost of an exceptional prime. -/
theorem bad_weight {B : Finset ℕ}
    (h : (45*(2^30:ℝ)^2 - 40*2^30)*weight B ≤ (2^30:ℝ)^6/2 * log 6) :
    weight B < 2^120/50 := by
  have hl : log (6:ℝ) < 1.799 := by
    rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [log_two_lt_d9, log_three_lt_d9]
  linarith

/-- Uniform weights for converting a sum of prime logarithms to a count. -/
theorem weight_bounds {P : Finset ℕ} (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159) :
    109*P.card ≤ weight P ∧ weight P ≤ 111*P.card := by
  have hb (p : ℕ) (h : p ∈ P) : 109 ≤ log (p:ℝ) ∧ log (p:ℝ) ≤ 111 := by
    obtain ⟨lo,hi⟩ := hp p h
    have lo' : (2:ℝ)^158 ≤ p := by exact_mod_cast lo
    have hi' : (p:ℝ) ≤ 2^159 := by exact_mod_cast hi
    have hlo := Real.log_le_log (by positivity : 0<(2:ℝ)^158) lo'
    have hp0 := lt_of_lt_of_le (by positivity : 0<(2:ℝ)^158) lo'
    have hhi := Real.log_le_log hp0 hi'
    rw [Real.log_pow] at hlo hhi
    norm_num1 at hlo hhi
    constructor <;> linarith [log_two_gt_d9,log_two_lt_d9]
  constructor
  · calc
      109*(P.card:ℝ) = ∑ _p ∈ P, (109:ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun p h => (hb p h).1
  · calc
      weight P ≤ ∑ _p ∈ P, (111:ℝ) := Finset.sum_le_sum fun p h => (hb p h).2
      _ = 111*(P.card:ℝ) := by simp [mul_comm]

/-- Uniform majorant of Lee's Corollary 1.1, table 1, row log x₀ = 30.
The negative additive constant in that estimate is discarded. -/
theorem lee_endpoint_error {x err : ℝ} (lo : (2:ℝ)^158 ≤ x) (hi : x ≤ 2^159)
    (he : err ≤ (log x/(8*π) + log ((2:ℝ)^30)/(2*π) + 5.66833) * sqrt x * log x) :
    err < 2^91 := by
  have hx := lt_of_lt_of_le (by norm_num : (1:ℝ)<2^158) lo
  have lx0 := Real.log_nonneg hx.le
  have lx := Real.log_le_log (zero_lt_one.trans hx) hi
  rw [Real.log_pow] at lx
  norm_num1 at lx
  have lx' : log x < 111 := by linarith [log_two_lt_d9]
  have lq : log ((2:ℝ)^30) < 21 := by
    rw [Real.log_pow]; norm_num1; linarith [log_two_lt_d9]
  have lp : 3 < π := Real.pi_gt_three
  have a : log x/(8*π) < 5 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have b : log ((2:ℝ)^30)/(2*π) < 4 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have hs : sqrt x ≤ 2^80 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, le_trans hi (by norm_num)⟩
  calc
    err ≤ _ := he
    _ ≤ 15 * sqrt x * log x := by
      gcongr
      linarith
    _ ≤ 15 * 2^80 * 111 := by gcongr
    _ < _ := by norm_num

/-- Lee's theta main term on a window, after two endpoint errors. -/
theorem window_weight {a b t₁ t₂ : ℝ} (h₁ : t₁ - a/2^29 < 2^91)
    (h₂ : b/2^29 - t₂ < 2^91) : (b-a)/2^29-2^92 < t₂-t₁ := by linarith

/-- Over the full dyadic prime band fewer than one in 25,000 primes can fail. -/
theorem band_failure_fraction {P B : Finset ℕ} (hsub : B ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159)
    (hP : 2^129-2^92 < weight P) (hB : weight B < 2^120/50) :
    25000*B.card < P.card := by
  have a := (weight_bounds (fun p h => hp p (hsub h))).1
  have b := (weight_bounds hp).2
  exact_mod_cast (show 25000*(B.card:ℝ) < (P.card:ℝ) by linarith)

/-- Turn the lower mass of the full set and the upper mass of the exceptions into
a concrete lower bound on the complement. -/
private theorem count_from_mass {P B : Finset ℕ} (hsub : B ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159) {M : ℕ}
    (hm : 111*(M:ℝ) < weight P - weight B) : M < (P \ B).card := by
  have eq : weight (P \ B) + weight B = weight P := Finset.sum_sdiff hsub
  have ub := (weight_bounds (P := P \ B) (fun p h => hp p (Finset.mem_sdiff.mp h).1)).2
  exact_mod_cast (show (M:ℝ) < ((P \ B).card:ℝ) by linarith)

/-- More than two to the 122 passing primes in the full band. -/
theorem band_passing_count {P B : Finset ℕ} (hsub : B ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159)
    (hP : 2^129-2^92 < weight P) (hB : weight B < 2^120/50) :
    2^122 < (P \ B).card := by
  apply count_from_mass hsub hp
  push_cast
  linarith

/-- Every subinterval of width two to the 144th has more than two to the 106th
passing primes under the same global exceptional-mass bound. -/
theorem narrow_passing_count {P B : Finset ℕ} (hsub : B ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159)
    (hP : 2^115-2^92 < weight P) (hB : weight B < 2^120/50) :
    2^106 < (P \ B).card := by
  apply count_from_mass hsub hp
  push_cast
  linarith

#print axioms bad_weight
#print axioms weight_bounds
#print axioms lee_endpoint_error
#print axioms band_failure_fraction
#print axioms band_passing_count
#print axioms narrow_passing_count

end
end ArkLib.ProximityGap.Frontier.SplitPrimeSixthDensity
