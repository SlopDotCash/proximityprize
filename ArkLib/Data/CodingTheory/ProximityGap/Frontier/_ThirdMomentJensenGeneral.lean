/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentJensen

/-!
# A parameterized discrete third-moment Jensen bound

This is the arbitrary-universe, arbitrary-incidence-threshold form of the
third-moment Jensen lemma.  The explicit hypothesis `2v <= Nt` is exactly the
condition that the forced average multiplicity is at least two, the monotone
range of the descending cubic.
-/

set_option autoImplicit false

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen

namespace ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral

/-- General real-valued discrete Jensen lower bound. -/
theorem thirdMoment_jensen_lower_real_general
    {U : Type*} [Fintype U] (m : U → ℕ) (v N t : ℕ)
    (hv : 0 < v) (hcard : Fintype.card U = v)
    (htwo : 2 * v ≤ N * t)
    (hsum : N * t ≤ ∑ i, m i) :
    let a : ℝ := (N : ℝ) * (t : ℝ) / (v : ℝ)
    (v : ℝ) * a * (a - 1) * (a - 2) ≤
      6 * ∑ i, ((m i).choose 3 : ℝ) := by
  let den : ℝ := v
  let w : U → ℝ := fun _ => 1 / den
  let avg : ℝ := ∑ i, w i * (m i : ℝ)
  let a : ℝ := (N : ℝ) * (t : ℝ) / den
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hden : 0 < den := by simpa only [den] using hvR
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
  have hsumR : (N : ℝ) * (t : ℝ) ≤ ∑ i, (m i : ℝ) := by
    exact_mod_cast hsum
  have ha_avg : a ≤ avg := by
    change (N : ℝ) * (t : ℝ) / den ≤ avg
    rw [havg_eq]
    exact (div_le_div_iff_of_pos_right hden).2 hsumR
  have ha_two : (2 : ℝ) ≤ a := by
    have htwoR : (2 : ℝ) * (v : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
      exact_mod_cast htwo
    change (2 : ℝ) ≤ (N : ℝ) * (t : ℝ) / den
    apply (le_div_iff₀ hden).2
    simpa only [den] using htwoR
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
  change den * a * (a - 1) * (a - 2) ≤
    6 * ∑ i, ((m i).choose 3 : ℝ)
  calc
    den * a * (a - 1) * (a - 2) =
        den * (descPochhammer ℝ 3).eval a := by
      rw [descPochhammer_three_eval]
      ring
    _ ≤ den * (descPochhammer ℝ 3).eval avg := by gcongr
    _ ≤ 6 * ∑ i, ((m i).choose 3 : ℝ) := by
      have hcross :=
        (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hden).1 hjensen'
      nlinarith

/-- Rational-valued general Jensen form used by exact arithmetic cores. -/
theorem thirdMoment_jensen_lower_rat_general
    {U : Type*} [Fintype U] (m : U → ℕ) (v N t : ℕ)
    (hv : 0 < v) (hcard : Fintype.card U = v)
    (htwo : 2 * v ≤ N * t)
    (hsum : N * t ≤ ∑ i, m i) :
    let a : ℚ := (N : ℚ) * (t : ℚ) / (v : ℚ)
    (v : ℚ) * a * (a - 1) * (a - 2) ≤
      6 * ∑ i, ((m i).choose 3 : ℚ) := by
  have hreal := thirdMoment_jensen_lower_real_general
    m v N t hv hcard htwo hsum
  dsimp only at hreal ⊢
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  simpa only [Nat.cast_sum] using hreal

end ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral

#print axioms
  ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral.thirdMoment_jensen_lower_rat_general
