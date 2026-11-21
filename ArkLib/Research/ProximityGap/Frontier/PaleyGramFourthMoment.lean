/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyProjectiveMoment
import Mathlib.Algebra.Order.Chebyshev

/-! # The double fourth moment of Paley Gram rows

The fourth moment over both shift parameters is a sum of squared complete
quartic character sums. Even root multiplicities account for at most three
pairings. A quartic estimate at constant `C` controls all other quadruples
with coefficient `C²`.
-/

namespace ProximityGap.PaleyGramFourthMoment

open Finset
open ArkLib.ProximityGap.Frontier
open R18FourthMomentTwist R20QuadFaceBridge R22StepanovAssembly R23ParameterChoice

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Inner product of two quadratic-character rows restricted to `A`. -/
def gram (A : Finset F) (t y : F) : ℤ :=
  ∑ a ∈ A, quadraticChar F (a - t) * quadraticChar F (a - y)

/-- Squaring each complete quartic correlation exactly accounts for the two
independent summation variables in the Gram moment. -/
theorem double_fourth_eq (A : Finset F) :
    ∑ t : F, ∑ y : F, gram A t y ^ 4 =
      ∑ z ∈ (A ×ˢ A) ×ˢ (A ×ˢ A), intQuartic z ^ 2 := by
  classical
  let Q := (A ×ˢ A) ×ˢ (A ×ˢ A)
  let J (z : (F × F) × (F × F)) (t : F) :=
    quadraticChar F ((t - z.1.1) * (t - z.1.2) * ((t - z.2.1) * (t - z.2.2)))
  have four (f : F → ℤ) :
      (∑ a ∈ A, f a) ^ 4 = ∑ z ∈ Q, (f z.1.1 * f z.1.2) * (f z.2.1 * f z.2.2) := by
    let pair (e : F × F) := f e.1 * f e.2
    have two : (∑ a ∈ A, f a) ^ 2 = ∑ e ∈ A ×ˢ A, pair e := by
      rw [pow_two, sum_mul_sum, sum_product]
    rw [show (∑ a ∈ A, f a) ^ 4 = ((∑ a ∈ A, f a) ^ 2) ^ 2 by ring, two, pow_two,
      sum_mul_sum]
    change _ = ∑ z ∈ (A ×ˢ A) ×ˢ (A ×ˢ A), pair z.1 * pair z.2
    conv_rhs => rw [sum_product]
  have expand (t y : F) : gram A t y ^ 4 = ∑ z ∈ Q, J z t * J z y := by
    have signs (a : F) : quadraticChar F (a - t) * quadraticChar F (a - y) =
        quadraticChar F (t - a) * quadraticChar F (y - a) := by
      rw [← map_mul, ← map_mul, show (a - t) * (a - y) = (t - a) * (y - a) by ring]
    rw [gram]
    simp_rw [signs]
    rw [four]
    exact sum_congr rfl fun z _ => by simp only [J, map_mul]; ring
  calc
    _ = ∑ t : F, ∑ z ∈ Q, ∑ y : F, J z t * J z y := by
      simp_rw [expand]
      exact sum_congr rfl fun t _ => sum_comm
    _ = ∑ z ∈ Q, (∑ t : F, J z t) * (∑ y : F, J z y) := by
      rw [sum_comm]
      simp only [← mul_sum, ← sum_mul]
    _ = _ := by simp only [Q, J, intQuartic, pow_two]

/-- An access point for any quartic Weil constant over the input domain.
No restriction on the size of the domain is needed. -/
theorem double_fourth_le_of_quartic (A : Finset F) {C : ℝ}
    (hW : QuarticWeilInputC (quadCharC F) A C) :
    ((∑ t : F, ∑ y : F, gram A t y ^ 4 : ℤ) : ℝ) ≤
      3 * (A.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 +
        (A.card : ℝ) ^ 4 * C ^ 2 * Fintype.card F := by
  classical
  let Q := (A ×ˢ A) ×ˢ (A ×ˢ A)
  let m : ℝ := A.card
  let q : ℝ := Fintype.card F
  let square (z : (F × F) × (F × F)) := (intQuartic z : ℝ) ^ 2
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hd : ∑ z ∈ Q.filter IsDegenerate, square z ≤ 3 * m ^ 2 * q ^ 2 := by
    have hcount : ((Q.filter IsDegenerate).card : ℝ) ≤ 3 * m ^ 2 := by
      dsimp only [Q, m]
      exact_mod_cast card_filter_degenerate_le A
    refine (sum_le_card_nsmul _ _ (q ^ 2) (fun z _ => ?_)).trans ?_
    · have h := norm_quadTerm_le_card (quadCharC F) z
      rw [norm_quadTerm_quadCharC] at h
      exact (sq_le_sq.mpr (by simpa only [abs_of_nonneg hq] using h))
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
  have hn : ∑ z ∈ Q.filter (fun z => ¬ IsDegenerate z), square z ≤ m ^ 4 * (C ^ 2 * q) := by
    have hcard : (Q.card : ℝ) = m ^ 4 := by simp [Q, m, card_product]; ring
    have hcount : ((Q.filter (fun z => ¬ IsDegenerate z)).card : ℝ) ≤ m ^ 4 := by
      rw [← hcard]
      exact_mod_cast card_le_card (filter_subset _ _)
    refine (sum_le_card_nsmul _ _ (C ^ 2 * q) (fun z hz => ?_)).trans ?_
    · obtain ⟨hzQ, hnd⟩ := mem_filter.mp hz
      have h := hW z hzQ hnd
      rw [norm_quadTerm_quadCharC] at h
      calc
        square z = |(intQuartic z : ℝ)| ^ 2 := (sq_abs _).symm
        _ ≤ (C * Real.sqrt q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt hq]
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcount (mul_nonneg (sq_nonneg _) hq)
  rw [double_fourth_eq]
  push_cast
  change ∑ z ∈ Q, square z ≤ 3 * m ^ 2 * q ^ 2 + m ^ 4 * C ^ 2 * q
  rw [← sum_filter_add_sum_filter_not Q IsDegenerate square, mul_assoc (m ^ 4)]
  exact add_le_add hd hn

/-- Unconditional finite-field bound with the in-tree Stepanov constant. -/
theorem double_fourth_le (hF : ringChar F ≠ 2) (A : Finset F) :
    ∑ t : F, ∑ y : F, gram A t y ^ 4 ≤
      3 * (A.card : ℤ) ^ 2 * (Fintype.card F : ℤ) ^ 2 +
        196 * (A.card : ℤ) ^ 4 * Fintype.card F := by
  have hw : QuarticWeilInputC (quadCharC F) A 14 := by
    convert quarticWeilInputC_of_cubicHasseC hF (k := 13) (by norm_num)
      (legendreCubicHasseC_unconditional hF) A using 1
    norm_num
  have h := double_fourth_le_of_quartic A hw
  norm_num at h
  rw [mul_comm ((A.card : ℝ) ^ 4) _] at h
  exact_mod_cast h

/-- At field order at least 3251 the improved Stepanov constant gives 64. -/
theorem double_fourth_le_of_large (hF : ringChar F ≠ 2) (hq : 3251 ≤ Fintype.card F)
    (A : Finset F) :
    ∑ t : F, ∑ y : F, gram A t y ^ 4 ≤
      3 * (A.card : ℤ) ^ 2 * (Fintype.card F : ℤ) ^ 2 +
        64 * (A.card : ℤ) ^ 4 * Fintype.card F := by
  have hw : QuarticWeilInputC (quadCharC F) A 8 := by
    convert quarticWeilInputC_of_cubicHasseC hF (k := 7) (by norm_num)
      (legendreCubicHasseC_49_of_large hF hq) A using 1
    norm_num
  have h := double_fourth_le_of_quartic A hw
  norm_num at h
  rw [mul_comm ((A.card : ℝ) ^ 4) _] at h
  exact_mod_cast h

/-- The untwisted Paley row after puncturing at `t` and inverting. -/
def chartRow (A : Finset F) (t z : F) : ℤ :=
  ∑ x ∈ PaleyProjectiveMoment.inverseImage A t, quadraticChar F (x - z)

private theorem char_inv {v : F} (hv : v ≠ 0) : quadraticChar F v⁻¹ = quadraticChar F v := by
  have h : quadraticChar F v⁻¹ * quadraticChar F v = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hv, map_one]
  rcases quadraticChar_dichotomy hv with hc | hc <;> rw [hc] at h ⊢ <;> linarith

private theorem chart_gram (A : Finset F) (t y : F) :
    chartRow A t (y - t)⁻¹ ^ 4 ≤ gram A t y ^ 4 := by
  classical
  have imageSum (z : F) : chartRow A t z =
      ∑ a ∈ A.erase t, quadraticChar F ((a - t)⁻¹ - z) := by
    rw [chartRow, PaleyProjectiveMoment.inverseImage, sum_image]
    intro a _ b _ h
    exact sub_left_inj.mp (inv_injective h)
  have unpuncture (f : F → ℤ) (h : f t = 0) : ∑ a ∈ A.erase t, f a = ∑ a ∈ A, f a := by
    by_cases ht : t ∈ A
    · simpa [h] using sum_erase_add A f ht
    · rw [erase_eq_of_notMem ht]
  rw [imageSum]
  by_cases hy : y = t
  · subst y
    simp only [sub_self, inv_zero, sub_zero]
    have hbound : |∑ a ∈ A.erase t, quadraticChar F (a - t)⁻¹| ≤ gram A t t := calc
      _ ≤ ∑ a ∈ A.erase t, |quadraticChar F (a - t)⁻¹| := abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ A.erase t, quadraticChar F (a - t) * quadraticChar F (a - t) := by
        apply sum_congr rfl
        intro a ha
        have hne := sub_ne_zero.mpr (mem_erase.mp ha).1
        rw [char_inv hne]
        rcases quadraticChar_dichotomy hne with h | h <;> rw [h] <;> norm_num
      _ = _ := unpuncture _ (by simp)
    rw [← (show Even 4 by decide).pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound 4
  · have hy' := sub_ne_zero.mpr hy
    let c := quadraticChar F (-1) * quadraticChar F (y - t)
    have hsign : c ^ 4 = 1 := by
      have ha := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
      have hb := quadraticChar_sq_one hy'
      rw [show c ^ 4 = (quadraticChar F (-1) ^ 2 * quadraticChar F (y - t) ^ 2) ^ 2 by
        dsimp [c]; ring, ha, hb]; norm_num
    have convertRow : (∑ a ∈ A.erase t, quadraticChar F ((a - t)⁻¹ - (y - t)⁻¹)) =
        c * gram A t y := by
      calc
        _ = ∑ a ∈ A.erase t, c * (quadraticChar F (a - t) * quadraticChar F (a - y)) := by
          apply sum_congr rfl
          intro a ha
          have ha' := sub_ne_zero.mpr (mem_erase.mp ha).1
          have harg : (a - t)⁻¹ - (y - t)⁻¹ =
              ((-1) * (a - y)) * ((a - t)⁻¹ * (y - t)⁻¹) := by field_simp; ring
          rw [harg]
          simp only [c, map_mul, char_inv ha', char_inv hy']
          ring
        _ = c * gram A t y := by
          rw [← mul_sum, gram, unpuncture _ (by simp)]
    rw [convertRow, mul_pow, hsign, one_mul]

/-- The zero target of the chart is covered by the diagonal Gram term, so
there is no extra error from that target. -/
theorem chart_moment_le_gram (A : Finset F) (t : F) :
    ∑ z : F, chartRow A t z ^ 4 ≤ ∑ y : F, gram A t y ^ 4 := by
  have he : Function.Bijective (fun y : F => (y - t)⁻¹) :=
    inv_bijective.comp (Equiv.subRight t).bijective
  rw [← he.sum_comp (fun z => chartRow A t z ^ 4)]
  exact sum_le_sum fun y _ => chart_gram A t y

/-- Every partner in the inverted chart is bounded by the same Gram row moment. -/
theorem partner_fourth_le (A B : Finset F) (t : F) :
    |∑ z ∈ B, chartRow A t z| ^ 4 ≤
      (B.card : ℤ) ^ 3 * ∑ y : F, gram A t y ^ 4 := by
  classical
  have hpow := pow_sum_le_card_mul_sum_pow (s := B)
    (f := fun z => |chartRow A t z|) (fun _ _ => abs_nonneg _) 3
  have hsubset : ∑ z ∈ B, chartRow A t z ^ 4 ≤ ∑ z : F, chartRow A t z ^ 4 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => Even.pow_nonneg (by decide) _)
  calc
    _ ≤ (∑ z ∈ B, |chartRow A t z|) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_sum_le_sum_abs _ _) 4
    _ ≤ (B.card : ℤ) ^ 3 * ∑ z ∈ B, chartRow A t z ^ 4 := by
      simpa only [Nat.reduceAdd, (show Even 4 by decide).pow_abs] using hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsubset.trans (chart_moment_le_gram A t)) (by positivity)

/-- Poles admitting any partner of size at least `b₀` with mean signed
discrepancy of magnitude at least `T`. The partner may depend on the pole. -/
noncomputable def exceptionalPoles (A : Finset F) (b₀ : ℕ) (T : ℝ) : Finset F :=
  univ.filter fun t => ∃ B : Finset F, b₀ ≤ B.card ∧
    T * B.card ≤ |((∑ z ∈ B, chartRow A t z : ℤ) : ℝ)|

/-- A simultaneous upper tail over all partners, in fourth-moment units. -/
theorem exceptionalPoles_le_moment (A : Finset F) {b₀ : ℕ} (hb : 0 < b₀) {T : ℝ}
    (hT : 0 ≤ T) :
    ((exceptionalPoles A b₀ T).card : ℝ) * (b₀ * T ^ 4) ≤
      ((∑ t : F, ∑ y : F, gram A t y ^ 4 : ℤ) : ℝ) := by
  classical
  let row (t : F) : ℝ := ((∑ y : F, gram A t y ^ 4 : ℤ) : ℝ)
  have hrow (t : F) : 0 ≤ row t := by
    dsimp only [row]
    exact_mod_cast sum_nonneg (fun y _ => (show (0 : ℤ) ≤ gram A t y ^ 4 by positivity))
  calc
    _ = ∑ _ ∈ exceptionalPoles A b₀ T, (b₀ : ℝ) * T ^ 4 := by simp
    _ ≤ ∑ t ∈ exceptionalPoles A b₀ T, row t := by
      refine sum_le_sum fun t ht => ?_
      obtain ⟨B, hcard, hbad⟩ := (mem_filter.mp ht).2
      have hpos : (0 : ℝ) < B.card := by exact_mod_cast lt_of_lt_of_le hb hcard
      have hlow := pow_le_pow_left₀ (mul_nonneg hT hpos.le) hbad 4
      have hupper : |((∑ z ∈ B, chartRow A t z : ℤ) : ℝ)| ^ 4 ≤ (B.card : ℝ) ^ 3 * row t := by
        dsimp only [row]
        exact_mod_cast partner_fourth_le A B t
      have hcancel : (B.card : ℝ) * T ^ 4 ≤ row t := by
        apply (mul_le_mul_iff_right₀ (pow_pos hpos 3)).mp
        calc
          _ = (T * (B.card : ℝ)) ^ 4 := by ring
          _ ≤ _ := hlow.trans hupper
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)).trans hcancel
    _ ≤ ∑ t : F, row t := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun t _ _ => hrow t)
    _ = _ := by simp [row]

/-- An unconditional exceptional-pole count at every odd field order. -/
theorem exceptionalPoles_le (hF : ringChar F ≠ 2) (A : Finset F) {b₀ : ℕ}
    (hb : 0 < b₀) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptionalPoles A b₀ T).card : ℝ) * (b₀ * T ^ 4) ≤
      3 * (A.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 +
        196 * (A.card : ℝ) ^ 4 * Fintype.card F := by
  refine (exceptionalPoles_le_moment A hb hT).trans ?_
  exact_mod_cast double_fourth_le hF A

/-- The exceptional-pole count with the sharper large-field constant. -/
theorem exceptionalPoles_le_of_large (hF : ringChar F ≠ 2) (hq : 3251 ≤ Fintype.card F)
    (A : Finset F) {b₀ : ℕ} (hb : 0 < b₀) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptionalPoles A b₀ T).card : ℝ) * (b₀ * T ^ 4) ≤
      3 * (A.card : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 +
        64 * (A.card : ℝ) ^ 4 * Fintype.card F := by
  refine (exceptionalPoles_le_moment A hb hT).trans ?_
  exact_mod_cast double_fourth_le_of_large hF hq A

end ProximityGap.PaleyGramFourthMoment

#print axioms ProximityGap.PaleyGramFourthMoment.double_fourth_eq
#print axioms ProximityGap.PaleyGramFourthMoment.double_fourth_le
#print axioms ProximityGap.PaleyGramFourthMoment.double_fourth_le_of_large

#print axioms ProximityGap.PaleyGramFourthMoment.exceptionalPoles_le
#print axioms ProximityGap.PaleyGramFourthMoment.exceptionalPoles_le_of_large
