/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Analysis.Real.Sqrt
import ArkLib.Research.ProximityGap.Frontier.PaleyPrescribedRectangle

/-! # Balanced prescribed rectangles at the square-root scale

The finite degree estimate with the integer parameter `a / 4` bounds the
squared relative discrepancy by an envelope tending to three quarters.
-/

namespace ProximityGap.PaleyBalancedLimit

open Filter
open scoped Topology BigOperators

/-- Upper bound for the squared relative discrepancy after rounding the quarter-size parameter. -/
noncomputable def envelope (p a b : ℝ) : ℝ := (1/2 + 2/a)^2 + (p/2 + 1)/(a*b)

/-- Bounding the rounding error uniformly gives an envelope depending only on the two sizes
and the field order. -/
theorem quarter_bound {a b p : ℕ} {s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (H : s^2 ≤ (b : ℝ)^2 * ((a : ℝ)-2*((a/4 : ℕ) : ℝ))^2 +
      4*b*((a/4*(p/2+1-a/4) : ℕ) : ℝ)) :
    (s / ((a : ℝ)*b))^2 ≤ envelope p a b := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have h₁ : 4*((a/4 : ℕ) : ℝ) ≤ a := by exact_mod_cast (show 4*(a/4) ≤ a by omega)
  have h₂ : (a : ℝ) ≤ 4*((a/4 : ℕ) : ℝ)+3 := by
    exact_mod_cast (show a ≤ 4*(a/4)+3 by omega)
  have h₃ : 2*((p/2+1-a/4 : ℕ) : ℝ) ≤ (p : ℝ)+2 := by
    exact_mod_cast (show 2*(p/2+1-a/4) ≤ p+2 by omega)
  have h₄ : ((a : ℝ)-2*((a/4 : ℕ) : ℝ))^2 ≤ ((a : ℝ)/2+2)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h₅ : 4*((a/4 : ℕ) : ℝ)*((p/2+1-a/4 : ℕ) : ℝ) ≤ (a : ℝ)*(p/2+1 : ℝ) :=
    mul_le_mul h₁ (by linarith) (by positivity) ha'.le
  have hmajor : s^2 ≤ (b : ℝ)^2*((a : ℝ)/2+2)^2 + b*a*(p/2+1 : ℝ) := by
    rw [Nat.cast_mul] at H
    nlinarith only [H, mul_le_mul_of_nonneg_left h₄ (sq_nonneg (b : ℝ)),
      mul_le_mul_of_nonneg_left h₅ hb'.le]
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos (mul_pos ha' hb'))]
  convert hmajor using 1
  unfold envelope
  field_simp

/-- If both sizes are asymptotic to the square root of the field order,
the squared-discrepancy envelope converges to `3 / 4`. -/
theorem tendsto_envelope {p a b : ℕ → ℝ} (hp : Tendsto p atTop atTop)
    (ha : Tendsto (fun n => a n / Real.sqrt (p n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => b n / Real.sqrt (p n)) atTop (𝓝 1)) :
    Tendsto (fun n => envelope (p n) (a n) (b n)) atTop (𝓝 (3/4)) := by
  have hp' := hp.eventually_gt_atTop 0
  have hr := Real.tendsto_sqrt_atTop.comp hp
  have ha' : Tendsto a atTop atTop :=
    (ha.pos_mul_atTop (by norm_num) hr).congr' (by
      filter_upwards [hp'] with n hn
      exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn).ne')
  have hden := ha.mul hb
  have hquot := ((tendsto_const_nhds (x := (1/2 : ℝ))).add
    (tendsto_inv_atTop_zero.comp hp)).div hden (by norm_num)
  have hfirst := ((tendsto_const_nhds (x := (1/2 : ℝ))).add
    ((tendsto_inv_atTop_zero.comp ha').const_mul 2)).pow 2
  convert (hfirst.add hquot).congr' ?_ using 1
  · norm_num
  filter_upwards [hp', ha.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hb.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn han hbn
  have ha0 : a n ≠ 0 := by intro h; simp [h] at han
  have hb0 : b n ≠ 0 := by intro h; simp [h] at hbn
  have hrp := Real.sq_sqrt hn.le
  have hrn := (Real.sqrt_pos.mpr hn).ne'
  dsimp [envelope]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [ha0, hb0, hn.ne', hrn]
  rw [hrp]
  ring

/-- For every positive error tolerance, the relative signed discrepancy is eventually below
`√3 / 2` plus that tolerance along any sequence of prime fields with both prescribed set
sizes asymptotic to `√p`. -/
theorem eventually_balanced_discrepancy (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (A B : (n : ℕ) → Finset (ZMod (p n))) (hp : Tendsto p atTop atTop)
    (ha : Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt (p n)) atTop (𝓝 1))
    (hb : Tendsto (fun n => ((B n).card : ℝ) / Real.sqrt (p n)) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (|∑ b ∈ B n, ∑ u ∈ A n, quadraticChar (ZMod (p n)) (b+u)| : ℝ) /
        ((A n).card * (B n).card : ℝ) < Real.sqrt 3/2 + ε := by
  have hpR : Tendsto (fun n => (p n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hp
  have hr := Real.tendsto_sqrt_atTop.comp hpR
  have hlim := (Real.continuous_sqrt.tendsto (3/4)).comp (tendsto_envelope hpR ha hb)
  have heq : Real.sqrt (3/4) = Real.sqrt 3/2 := by
    rw [Real.sqrt_div (by norm_num), show (4:ℝ) = 2^2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [heq] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)),
    hr.eventually_ge_atTop 8, ha.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num)),
    ha.eventually (gt_mem_nhds (show (1:ℝ)<2 by norm_num)),
    hb.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num)), hp.eventually_gt_atTop 2]
    with n hlimn hrn hla hua hlb hpn
  dsimp at hrn hla hua hlb hlimn
  let a := (A n).card
  let b := (B n).card
  let s := ∑ v ∈ B n, ∑ u ∈ A n, quadraticChar (ZMod (p n)) (v+u)
  have hrpos : 0 < Real.sqrt (p n) := by linarith
  have hla' := (lt_div_iff₀ hrpos).mp hla
  have hua' := (div_lt_iff₀ hrpos).mp hua
  have hlb' := (lt_div_iff₀ hrpos).mp hlb
  have ha4 : 4 ≤ a := by
    have : (4:ℝ) ≤ (A n).card := by linarith
    exact_mod_cast this
  have hb1 : 0 < b := by
    have : (0:ℝ) < (B n).card := by linarith
    exact_mod_cast this
  have ha2 : 2*a ≤ p n := by
    have sqr := Real.sq_sqrt (show 0 ≤ (p n : ℝ) by positivity)
    have : 2*((A n).card : ℝ) ≤ p n := by
      nlinarith [mul_nonneg hrpos.le (show 0 ≤ Real.sqrt (p n)-4 by linarith)]
    exact_mod_cast this
  have H := PaleyPrescribedRectangle.discrepancy_sq (p := p n) (by omega) (A n) (B n)
    (by change 2 ≤ a; omega) (by change a ≤ p n / 2 + 1; omega) (x := a/4)
    (by omega) (by change 2*(a/4) ≤ a; omega)
  have Hs : |s|^2 ≤ (b : ℤ)^2 * ((a : ℤ)-2*(a/4 : ℕ))^2 +
      4*b*(a/4*(p n/2+1-a/4) : ℕ) :=
    (pow_le_pow_left₀ (abs_nonneg s) (le_add_of_nonneg_right (Int.natCast_nonneg _)) 2).trans H
  have H' := quarter_bound (s := (|s| : ℝ)) (p := p n) (by omega : 0 < a) hb1
    (by
      have hh := (Int.cast_le (R := ℝ)).mpr Hs
      simpa only [Int.cast_pow, Int.cast_abs, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
        Int.cast_sub, Int.cast_add] using hh)
  simpa only [a, b, s, Int.cast_sum] using (Real.le_sqrt_of_sq_le H').trans_lt hlimn

#print axioms quarter_bound
#print axioms tendsto_envelope
#print axioms eventually_balanced_discrepancy

end ProximityGap.PaleyBalancedLimit
