/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Tactic

/-!
# The discrete Jensen lower bound for the half-predecessor third moment

For `2h` coordinates with multiplicities `m_i` and total incidence at least `N(h+1)`, this file
proves the exact lower bound used by the rate-`1/16` half-predecessor argument:

```text
2h * a(a-1)(a-2) <= 6 * sum_i choose(m_i,3),
a = N(h+1)/(2h).
```

The proof uses Mathlib's Jensen theorem for `Nat.choose`.  That theorem applies a globally convex
piecewise descending-Pochhammer extension, so multiplicities `0`, `1`, and `2` introduce no hidden
continuous-convexity assumption.  This formally validates the paper proof's step `(L)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen

/-- The descending Pochhammer polynomial of order three is the expected cubic. -/
theorem descPochhammer_three_eval (x : ℝ) :
    (descPochhammer ℝ 3).eval x = x * (x - 1) * (x - 2) := by
  norm_num [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ]

/-- **Discrete third-moment Jensen bound.**  On `2h` coordinates, total incidence at least
`N(h+1)` forces the exact cubic lower bound at the average multiplicity.  No lower bound on the
individual multiplicities is required. -/
theorem thirdMoment_jensen_lower_real
    {U : Type*} [Fintype U] (m : U → ℕ) (h N : ℕ)
    (hh : 0 < h) (hcard : Fintype.card U = 2 * h)
    (hN : 2 * h + 1 ≤ N)
    (hsum : N * (h + 1) ≤ ∑ i, m i) :
    let a : ℝ := (N : ℝ) * ((h : ℝ) + 1) / (2 * (h : ℝ))
    2 * (h : ℝ) * a * (a - 1) * (a - 2) ≤
      6 * ∑ i, ((m i).choose 3 : ℝ) := by
  let den : ℝ := 2 * (h : ℝ)
  let w : U → ℝ := fun _ => 1 / den
  let avg : ℝ := ∑ i, w i * (m i : ℝ)
  let a : ℝ := (N : ℝ) * ((h : ℝ) + 1) / den
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hden : 0 < den := by positivity
  have hcardR : (Fintype.card U : ℝ) = den := by
    simp only [den]
    exact_mod_cast hcard
  have hw0 : ∀ i ∈ (Finset.univ : Finset U), 0 ≤ w i := by
    intro i hi
    simp only [w]
    positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset U), w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcardR]
    field_simp
  have havg_eq : avg = (∑ i, (m i : ℝ)) / den := by
    simp only [avg, w]
    rw [← Finset.mul_sum]
    simp [div_eq_mul_inv, mul_comm]
  have hsumR :
      (N : ℝ) * ((h : ℝ) + 1) ≤ ∑ i, (m i : ℝ) := by
    exact_mod_cast hsum
  have ha_avg : a ≤ avg := by
    change (N : ℝ) * ((h : ℝ) + 1) / den ≤ avg
    rw [havg_eq]
    exact (div_le_div_iff_of_pos_right hden).2 hsumR
  have ha_two : (2 : ℝ) ≤ a := by
    have hNR : 2 * (h : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hprod := mul_le_mul_of_nonneg_right hNR
      (show (0 : ℝ) ≤ (h : ℝ) + 1 by positivity)
    change (2 : ℝ) ≤ (N : ℝ) * ((h : ℝ) + 1) / den
    apply (le_div_iff₀ hden).2
    dsimp only [den]
    nlinarith [sq_nonneg ((h : ℝ) - 1)]
  have havg_two : (2 : ℝ) ≤ avg := ha_two.trans ha_avg
  have hjensen := descPochhammer_eval_div_factorial_le_sum_choose
    (n := 3) (by norm_num) (t := (Finset.univ : Finset U)) m w hw0 hw1 (by
      norm_num
      exact havg_two)
  have hmono :
      (descPochhammer ℝ 3).eval a ≤ (descPochhammer ℝ 3).eval avg :=
    monotoneOn_descPochhammer_eval 3 (by
      simp only [Set.mem_Ici]
      norm_num
      linarith) (by
      simp only [Set.mem_Ici]
      norm_num
      linarith) ha_avg
  have hjensen' :
      (descPochhammer ℝ 3).eval avg / 6 ≤
        (∑ i, ((m i).choose 3 : ℝ)) / den := by
    change (descPochhammer ℝ 3).eval avg / 6 ≤ _
    calc
      (descPochhammer ℝ 3).eval avg / 6
          ≤ ∑ i, w i * ((m i).choose 3 : ℝ) := by
            simpa only [Nat.factorial, Nat.cast_ofNat] using hjensen
      _ = (∑ i, ((m i).choose 3 : ℝ)) / den := by
        simp only [w, one_div_mul_eq_div, Finset.sum_div]
  change den * a * (a - 1) * (a - 2) ≤ 6 * ∑ i, ((m i).choose 3 : ℝ)
  calc
    den * a * (a - 1) * (a - 2) = den * (descPochhammer ℝ 3).eval a := by
      rw [descPochhammer_three_eval]
      ring
    _
        ≤ den * (descPochhammer ℝ 3).eval avg := by gcongr
    _ ≤ 6 * ∑ i, ((m i).choose 3 : ℝ) := by
      have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hden).1 hjensen'
      nlinarith

/-- Rational-valued form used directly by the `lowerSix` / `gapQuadratic` numeric core. -/
theorem thirdMoment_jensen_lower_rat
    {U : Type*} [Fintype U] (m : U → ℕ) (h N : ℕ)
    (hh : 0 < h) (hcard : Fintype.card U = 2 * h)
    (hN : 2 * h + 1 ≤ N)
    (hsum : N * (h + 1) ≤ ∑ i, m i) :
    let a : ℚ := (N : ℚ) * ((h : ℚ) + 1) / (2 * (h : ℚ))
    2 * (h : ℚ) * a * (a - 1) * (a - 2) ≤
      6 * ∑ i, ((m i).choose 3 : ℚ) := by
  have hreal := thirdMoment_jensen_lower_real m h N hh hcard hN hsum
  dsimp only at hreal ⊢
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  simpa only [Nat.cast_sum] using hreal

end ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen.descPochhammer_three_eval
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen.thirdMoment_jensen_lower_real
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen.thirdMoment_jensen_lower_rat
