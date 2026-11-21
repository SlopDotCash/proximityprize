/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Mean logarithmic mass of sums of six roots of unity

For every primitive complex root of order greater than one, the sum over all
ordered six-letter words of the logarithm of the absolute value of the word sum
is at most half the number of words times log 6. The zero sums contribute zero,
as required when a zero cyclotomic norm is omitted from a product.
-/

set_option autoImplicit false
open Finset
namespace ArkLib.ProximityGap.Frontier.CyclotomicMeanLogMass

/-- Sum a statistic over the endpoints of all ordered words in a fixed alphabet. -/
noncomputable def tally {n : ℕ} (z : Fin n → ℂ) (f : ℂ → ℝ) : ℕ → ℂ → ℝ
  | 0, x => f x
  | k+1, x => ∑ i, tally z f k (x+z i)

private theorem tally_mono {n : ℕ} (z : Fin n → ℂ) {f g : ℂ → ℝ}
    (h : ∀ x, f x ≤ g x) (k : ℕ) (x : ℂ) : tally z f k x ≤ tally z g k x := by
  induction k generalizing x with
  | zero => exact h x
  | succ k ih => exact sum_le_sum fun i _ => ih (x+z i)

private theorem one_step {n : ℕ} (z : Fin n → ℂ) (hs : ∑ i, z i = 0)
    (hn : ∀ i, Complex.normSq (z i) = 1) (x : ℂ) :
    ∑ i, Complex.normSq (x+z i) = n * (Complex.normSq x+1) := by
  have hr : ∑ i, (z i).re = 0 := by simpa using congrArg Complex.re hs
  have hi : ∑ i, (z i).im = 0 := by simpa using congrArg Complex.im hs
  have hform (i : Fin n) : Complex.normSq (x+z i) = Complex.normSq x + 1 +
      2*x.re*(z i).re + 2*x.im*(z i).im := by
    rw [← hn i]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  simp_rw [hform]
  simp only [sum_add_distrib, ← Finset.mul_sum, hr, hi, mul_zero, add_zero, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Exact quadratic mass of all words for any zero-sum alphabet on the unit circle. -/
theorem tally_affine_normSq {n : ℕ} (z : Fin n → ℂ) (hs : ∑ i, z i = 0)
    (hn : ∀ i, Complex.normSq (z i) = 1) (a b : ℝ) (k : ℕ) (x : ℂ) :
    tally z (fun y => a*Complex.normSq y+b) k x =
      (n:ℝ)^k * (a*(Complex.normSq x+k)+b) := by
  induction k generalizing x with
  | zero => simp [tally]
  | succ k ih =>
    simp only [tally, ih, ← Finset.mul_sum, sum_add_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, one_step z hs hn x, pow_succ, Nat.cast_succ]
    ring

private theorem log_norm_bound (x : ℂ) :
    Real.log ‖x‖ ≤ (1/12:ℝ)*Complex.normSq x + (Real.log 6-1)/2 := by
  by_cases hx : x=0
  · subst x
    have hlog : 1 ≤ Real.log 6 := (Real.le_log_iff_exp_le (by norm_num)).mpr
      (Real.exp_one_lt_three.le.trans (by norm_num))
    simp only [norm_zero, Real.log_zero, Complex.normSq_zero, mul_zero, zero_add]
    linarith
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hh := Real.log_le_sub_one_of_pos (show 0 < ‖x‖^2/6 by positivity)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hh
    rw [Complex.normSq_eq_norm_sq]
    push_cast at hh
    linarith

/-- Bound the literal ordered complex six-word logarithm sum, with zero words omitted
by the convention log 0 = 0. No assumption on the number of such words is used. -/
theorem sixth_root_log_mass {n : ℕ} (hn : 1 < n) {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) :
    tally (fun i : Fin n => ζ^i.val) (fun x => Real.log ‖x‖) 6 0 ≤
      (n:ℝ)^6 * (Real.log 6/2) := by
  let z (i : Fin n) := ζ^i.val
  have hsum : ∑ i, z i = 0 := by
    simpa only [z, Fin.sum_univ_eq_sum_range] using hz.geom_sum_eq_zero hn
  have hnorm (i : Fin n) : Complex.normSq (z i) = 1 := by
    simp [z, Complex.normSq_eq_norm_sq, norm_pow, hz.norm'_eq_one (by omega)]
  calc
    _ ≤ _ := tally_mono z log_norm_bound 6 0
    _ = _ := by
      rw [tally_affine_normSq z hsum hnorm]
      simp only [Complex.normSq_zero, zero_add, Nat.cast_ofNat]
      ring

/-- The aggregate logarithmic excess budget gives an integer cap beyond the
first production scale. The calculation uses the rational bound log₂ 6 ≤ 106/41. -/
theorem production_bad_prime_cap (c : ℕ)
    (hcap : (c:ℝ) * (45*(2^30:ℝ)^2-39*(2^30)) * Real.log ((2:ℝ)^158) ≤
      (2^30:ℝ)^6 * (Real.log 6/2)) :
    c ≤ 241669527060695186377734665249132 := by
  have hlog := Real.log_le_log (show 0 < (6:ℝ)^41 by positivity)
    (show (6:ℝ)^41 ≤ 2^106 by norm_num)
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog hcap
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_contra! hc
  have hc' : (241669527060695186377734665249133:ℝ) ≤ c := by exact_mod_cast hc
  have hlow := mul_le_mul_of_nonneg_right hc' hpos.le
  nlinarith only [hlog, hcap, hpos, hlow]

/-- Refined cap using the maximal minor after removing the characteristic-zero nullity. -/
theorem production_minor_bad_prime_cap (c : ℕ)
    (hcap : (c:ℝ) * (45*(2^30:ℝ)^2-39*(2^30)) * Real.log ((2:ℝ)^158) ≤
      ((2^30:ℝ)^6-18569100537399236459128422400) * (Real.log 6/2)) :
    c ≤ 241669527060695186377734662320845 := by
  have hlog := Real.log_le_log (show 0 < (6:ℝ)^41 by positivity)
    (show (6:ℝ)^41 ≤ 2^106 by norm_num)
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog hcap
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_contra! hc
  have hc' : (241669527060695186377734662320846:ℝ) ≤ c := by exact_mod_cast hc
  have hlow := mul_le_mul_of_nonneg_right hc' hpos.le
  nlinarith only [hlog, hcap, hpos, hlow]

#print axioms production_minor_bad_prime_cap
#print axioms production_bad_prime_cap
#print axioms tally_affine_normSq
#print axioms sixth_root_log_mass

end ArkLib.ProximityGap.Frontier.CyclotomicMeanLogMass
