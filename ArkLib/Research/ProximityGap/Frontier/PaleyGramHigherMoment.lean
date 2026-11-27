/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyHigherMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# All-order double even moments of Paley Gram rows and inverted-chart pole tails

This file generalizes `PaleyGramFourthMoment.lean` from order `4` to **arbitrary even order `2r`**
(`r ≥ 1`), closing the written-only higher-moment gap of `paley-cross-ratio-moments.md`
completely unconditionally and axiom-clean (zero external Weil axioms):

* `double_even_eq`: `∑ t : F, ∑ y : F, gram A t y ^ (2 * r) = ∑ a ∈ tupleSet A (2 * r), tupleCharSum a ^ 2`.
* `double_even_le`: `≤ (2r - 1)!! · |A|^r · q^2 + 81 r^2 · |A|^(2r) · q`.
* `chart_moment_le_gram`: `∑ z : F, chartRow A t z ^ (2 * r) ≤ ∑ y : F, gram A t y ^ (2 * r)`.
* `exceptionalPoles_le`: simultaneous over ALL partners `B` of size `≥ b₀`,
  `|exceptionalPoles A b₀ T| · b₀ · T^(2r) ≤ (2r - 1)!! · |A|^r · q^2 + 81 r^2 · |A|^(2r) · q`.
* `exceptionalPoles_power_saving`: shatters the fourth-moment `|A|^2 b₀ ≫ q` (`q^{1/3}`) barrier
  all the way down to **arbitrary polynomial sizes `|A| ≥ q^{1/r}` and `b₀ ≥ q^η`** (`|A|, b₀ ≥ q^ε`),
  giving `|exceptionalPoles A b₀ (|A| q^{-δ})| ≤ ((2r-1)!! + 81 r^2) · q^{1 - η + 2rδ}`!
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleyGramHigherMoment

open Finset ProximityGap.PaleyHigherMoments

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Double `2r`-th Gram moment identity and unconditional upper bound -/

/-- Inner product of two quadratic-character rows restricted to `A`. -/
def gram (A : Finset F) (t y : F) : ℤ :=
  ∑ a ∈ A, quadraticChar F (a - t) * quadraticChar F (a - y)

/-- **Exact double `2r`-th Gram moment identity**:
`∑ t : F, ∑ y : F, gram A t y ^ (2 * r) = ∑ a ∈ tupleSet A (2 * r), (tupleCharSum a) ^ 2`. -/
theorem double_even_eq (A : Finset F) (r : ℕ) :
    ∑ t : F, ∑ y : F, gram A t y ^ (2 * r) =
      ∑ a ∈ tupleSet A (2 * r), (tupleCharSum a) ^ 2 := by
  classical
  let Q := tupleSet A (2 * r)
  let J (a : Fin (2 * r) → F) (t : F) : ℤ := ∏ i : Fin (2 * r), quadraticChar F (t - a i)
  have hexpand (t y : F) : gram A t y ^ (2 * r) = ∑ a ∈ Q, J a t * J a y := by
    have hsign (x : F) : quadraticChar F (x - t) * quadraticChar F (x - y) =
        quadraticChar F (t - x) * quadraticChar F (y - x) := by
      rw [← map_mul, ← map_mul, show (x - t) * (x - y) = (t - x) * (y - x) by ring]
    unfold gram
    simp_rw [hsign]
    calc (∑ x ∈ A, quadraticChar F (t - x) * quadraticChar F (y - x)) ^ (2 * r)
        = ∑ a ∈ Q, ∏ i : Fin (2 * r), (quadraticChar F (t - a i) * quadraticChar F (y - a i)) :=
            pow_sum_eq_sum_tupleSet A (2 * r) fun x => quadraticChar F (t - x) * quadraticChar F (y - x)
      _ = ∑ a ∈ Q, J a t * J a y := by
            refine Finset.sum_congr rfl fun a _ => ?_
            dsimp only [J]
            rw [Finset.prod_mul_distrib]
  calc ∑ t : F, ∑ y : F, gram A t y ^ (2 * r)
      = ∑ t : F, ∑ a ∈ Q, ∑ y : F, J a t * J a y := by
          simp_rw [hexpand]
          exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ a ∈ Q, (∑ t : F, J a t) * (∑ y : F, J a y) := by
          rw [Finset.sum_comm]
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ a ∈ Q, (tupleCharSum a) ^ 2 := by
          simp only [J, tupleCharSum, pow_two]

/-- **Unconditional all-order double `2r`-th Gram moment bound** for every odd-characteristic
finite field `F`, every `r ≥ 1`, and every `A : Finset F`. -/
theorem double_even_le (hF : ringChar F ≠ 2) (A : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    ((∑ t : F, ∑ y : F, gram A t y ^ (2 * r) : ℤ) : ℝ) ≤
      (doubleFact r : ℝ) * (A.card : ℝ) ^ r * (Fintype.card F : ℝ) ^ 2 +
        (81 * (r : ℝ) ^ 2) * (A.card : ℝ) ^ (2 * r) * Fintype.card F := by
  rw [double_even_eq]
  exact sum_sq_tupleCharSum_le hF A hr

/-! ## 2. Inverted-chart rows and simultaneous exceptional-pole tail bounds -/

/-- The punctured-and-inverted image `{ (a - t)⁻¹ : a ∈ A \ {t} }`. -/
def inverseImage (A : Finset F) (t : F) : Finset F :=
  (A.erase t).image fun a => (a - t)⁻¹

/-- The untwisted Paley row after puncturing at `t` and inverting. -/
def chartRow (A : Finset F) (t z : F) : ℤ :=
  ∑ x ∈ inverseImage A t, quadraticChar F (x - z)

private theorem char_inv {v : F} (hv : v ≠ 0) : quadraticChar F v⁻¹ = quadraticChar F v := by
  have h : quadraticChar F v⁻¹ * quadraticChar F v = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hv, map_one]
  rcases quadraticChar_dichotomy hv with hc | hc <;> rw [hc] at h ⊢ <;> linarith

private theorem chart_gram_even (A : Finset F) (t y : F) (r : ℕ) :
    chartRow A t (y - t)⁻¹ ^ (2 * r) ≤ gram A t y ^ (2 * r) := by
  classical
  have imageSum (z : F) : chartRow A t z =
      ∑ a ∈ A.erase t, quadraticChar F ((a - t)⁻¹ - z) := by
    rw [chartRow, inverseImage, Finset.sum_image]
    intro a _ b _ h
    exact sub_left_inj.mp (inv_injective h)
  have unpuncture (f : F → ℤ) (h : f t = 0) : ∑ a ∈ A.erase t, f a = ∑ a ∈ A, f a := by
    by_cases ht : t ∈ A
    · simpa [h] using Finset.sum_erase_add A f ht
    · rw [Finset.erase_eq_of_notMem ht]
  rw [imageSum]
  by_cases hy : y = t
  · subst y
    simp only [sub_self, inv_zero, sub_zero]
    have hbound : |∑ a ∈ A.erase t, quadraticChar F (a - t)⁻¹| ≤ gram A t t := by
      calc |∑ a ∈ A.erase t, quadraticChar F (a - t)⁻¹|
          ≤ ∑ a ∈ A.erase t, |quadraticChar F (a - t)⁻¹| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a ∈ A.erase t, quadraticChar F (a - t) * quadraticChar F (a - t) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            have hne := sub_ne_zero.mpr (Finset.mem_erase.mp ha).1
            rw [char_inv hne]
            rcases quadraticChar_dichotomy hne with h | h <;> rw [h] <;> decide
        _ = gram A t t := unpuncture _ (by simp)
    rw [← (even_two_mul r).pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbound (2 * r)
  · have hy' := sub_ne_zero.mpr hy
    let c : ℤ := quadraticChar F (-1) * quadraticChar F (y - t)
    have hsign : c ^ (2 * r) = 1 := by
      have ha := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
      have hb := quadraticChar_sq_one hy'
      have hc2 : c ^ 2 = 1 := by
        dsimp only [c]
        rw [mul_pow, ha, hb, one_mul]
      rw [pow_mul, hc2, one_pow]
    have convertRow : (∑ a ∈ A.erase t, quadraticChar F ((a - t)⁻¹ - (y - t)⁻¹)) =
        c * gram A t y := by
      calc ∑ a ∈ A.erase t, quadraticChar F ((a - t)⁻¹ - (y - t)⁻¹)
          = ∑ a ∈ A.erase t, c * (quadraticChar F (a - t) * quadraticChar F (a - y)) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            have ha' := sub_ne_zero.mpr (Finset.mem_erase.mp ha).1
            have harg : (a - t)⁻¹ - (y - t)⁻¹ =
                ((-1) * (a - y)) * ((a - t)⁻¹ * (y - t)⁻¹) := by field_simp [ha', hy']; ring
            rw [harg]
            simp only [c, map_mul, char_inv ha', char_inv hy']
            ring
        _ = c * gram A t y := by
            rw [← Finset.mul_sum, gram, unpuncture _ (by simp)]
    rw [convertRow, mul_pow, hsign, one_mul]

/-- The inverted-chart `2r`-th row moment is bounded by the `2r`-th Gram row moment. -/
theorem chart_moment_le_gram (A : Finset F) (t : F) (r : ℕ) :
    ∑ z : F, chartRow A t z ^ (2 * r) ≤ ∑ y : F, gram A t y ^ (2 * r) := by
  have he : Function.Bijective (fun y : F => (y - t)⁻¹) :=
    inv_bijective.comp (Equiv.subRight t).bijective
  rw [← he.sum_comp (fun z => chartRow A t z ^ (2 * r))]
  exact Finset.sum_le_sum fun y _ => chart_gram_even A t y r

/-- Every partner `B` in the inverted chart at pole `t` is bounded by the `2r`-th Gram moment. -/
theorem partner_even_le (A B : Finset F) (t : F) {r : ℕ} (hr : 1 ≤ r) :
    |∑ z ∈ B, chartRow A t z| ^ (2 * r) ≤
      (B.card : ℤ) ^ (2 * r - 1) * ∑ y : F, gram A t y ^ (2 * r) := by
  classical
  have hpow := pow_sum_le_card_mul_sum_pow (s := B)
    (f := fun z => |chartRow A t z|) (fun _ _ => abs_nonneg _) (2 * r - 1)
  have hidx : (2 * r - 1) + 1 = 2 * r := by omega
  rw [hidx] at hpow
  have heven : Even (2 * r) := even_two_mul r
  have hsubset : ∑ z ∈ B, chartRow A t z ^ (2 * r) ≤ ∑ z : F, chartRow A t z ^ (2 * r) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun _ _ _ => heven.pow_nonneg _)
  calc |∑ z ∈ B, chartRow A t z| ^ (2 * r)
      ≤ (∑ z ∈ B, |chartRow A t z|) ^ (2 * r) :=
        pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (2 * r)
    _ ≤ (B.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ B, |chartRow A t z| ^ (2 * r) := hpow
    _ = (B.card : ℤ) ^ (2 * r - 1) * ∑ z ∈ B, chartRow A t z ^ (2 * r) := by
        simp only [heven.pow_abs]
    _ ≤ (B.card : ℤ) ^ (2 * r - 1) * ∑ y : F, gram A t y ^ (2 * r) :=
        mul_le_mul_of_nonneg_left (hsubset.trans (chart_moment_le_gram A t r)) (by positivity)

/-- Poles `t` admitting ANY partner `B` of size `≥ b₀` with mean signed discrepancy `≥ T`. -/
noncomputable def exceptionalPoles (A : Finset F) (b₀ : ℕ) (T : ℝ) : Finset F :=
  Finset.univ.filter fun t => ∃ B : Finset F, b₀ ≤ B.card ∧
    T * B.card ≤ |((∑ z ∈ B, chartRow A t z : ℤ) : ℝ)|

/-- Simultaneous upper tail over all partners in `2r`-th moment units. -/
theorem exceptionalPoles_le_moment (A : Finset F) {b₀ : ℕ} (hb : 0 < b₀) {T : ℝ}
    (hT : 0 ≤ T) {r : ℕ} (hr : 1 ≤ r) :
    ((exceptionalPoles A b₀ T).card : ℝ) * ((b₀ : ℝ) * T ^ (2 * r)) ≤
      ((∑ t : F, ∑ y : F, gram A t y ^ (2 * r) : ℤ) : ℝ) := by
  classical
  let row (t : F) : ℝ := ((∑ y : F, gram A t y ^ (2 * r) : ℤ) : ℝ)
  have heven : Even (2 * r) := even_two_mul r
  have hrow (t : F) : 0 ≤ row t := by
    dsimp only [row]
    exact_mod_cast Finset.sum_nonneg (fun y _ => heven.pow_nonneg (gram A t y))
  calc ((exceptionalPoles A b₀ T).card : ℝ) * ((b₀ : ℝ) * T ^ (2 * r))
      = ∑ _t ∈ exceptionalPoles A b₀ T, (b₀ : ℝ) * T ^ (2 * r) := by simp
    _ ≤ ∑ t ∈ exceptionalPoles A b₀ T, row t := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨B, hcard, hbad⟩ := (Finset.mem_filter.mp ht).2
        have hpos : (0 : ℝ) < B.card := by exact_mod_cast lt_of_lt_of_le hb hcard
        have hlow := pow_le_pow_left₀ (mul_nonneg hT hpos.le) hbad (2 * r)
        have hupper : |((∑ z ∈ B, chartRow A t z : ℤ) : ℝ)| ^ (2 * r) ≤
            (B.card : ℝ) ^ (2 * r - 1) * row t := by
          dsimp only [row]
          exact_mod_cast partner_even_le A B t hr
        have hcancel : (B.card : ℝ) * T ^ (2 * r) ≤ row t := by
          apply le_of_mul_le_mul_left (a := (B.card : ℝ) ^ (2 * r - 1)) _ (pow_pos hpos (2 * r - 1))
          have hpowB : (B.card : ℝ) ^ (2 * r - 1) * (B.card : ℝ) = (B.card : ℝ) ^ (2 * r) := by
            rw [← pow_succ, show (2 * r - 1) + 1 = 2 * r by omega]
          calc (B.card : ℝ) ^ (2 * r - 1) * ((B.card : ℝ) * T ^ (2 * r))
              = (T * (B.card : ℝ)) ^ (2 * r) := by
                  rw [mul_pow, ← hpowB]; ring
            _ ≤ (B.card : ℝ) ^ (2 * r - 1) * row t := hlow.trans hupper
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)).trans hcancel
    _ ≤ ∑ t : F, row t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun t _ _ => hrow t)
    _ = ((∑ t : F, ∑ y : F, gram A t y ^ (2 * r) : ℤ) : ℝ) := by simp [row]

/-- **Unconditional all-order exceptional-pole bound** for every odd-characteristic finite field `F`
and every `r ≥ 1`. -/
theorem exceptionalPoles_le (hF : ringChar F ≠ 2) (A : Finset F) {b₀ : ℕ}
    (hb : 0 < b₀) {T : ℝ} (hT : 0 ≤ T) {r : ℕ} (hr : 1 ≤ r) :
    ((exceptionalPoles A b₀ T).card : ℝ) * ((b₀ : ℝ) * T ^ (2 * r)) ≤
      (doubleFact r : ℝ) * (A.card : ℝ) ^ r * (Fintype.card F : ℝ) ^ 2 +
        (81 * (r : ℝ) ^ 2) * (A.card : ℝ) ^ (2 * r) * Fintype.card F :=
  (exceptionalPoles_le_moment A hb hT hr).trans (double_even_le hF A hr)

/-- **All-polynomial-size simultaneous inverted-chart power saving**:
Shatters the fourth-moment `|A|^2 b₀ ≫ q` (`q^{1/3}`) barrier down to **all polynomial sizes**
`|A| ≥ q^{1/r}` and `b₀ ≥ q^η` (`r ≥ 1`, `η > 0`), showing that for any `δ ≥ 0`,
`|exceptionalPoles A b₀ (|A| q^{-δ})| ≤ ((2r-1)!! + 81 r^2) · q^{1 - η + 2rδ}`
(so taking `δ = η / (4r)` makes the bad-pole fraction `≤ C_r · q^{-η/2} → 0`!). -/
theorem exceptionalPoles_power_saving (hF : ringChar F ≠ 2) (A : Finset F)
    {b₀ : ℕ} (hb : 0 < b₀) {r : ℕ} (hr : 1 ≤ r)
    (η δ : ℝ) (hA : (Fintype.card F : ℝ) ^ (1 / (r : ℝ)) ≤ A.card)
    (hb_size : (Fintype.card F : ℝ) ^ η ≤ b₀) :
    ((exceptionalPoles A b₀ ((A.card : ℝ) * (Fintype.card F : ℝ) ^ (-δ))).card : ℝ) ≤
      ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) *
        (Fintype.card F : ℝ) ^ (1 - η + (2 * r : ℝ) * δ) := by
  let q : ℝ := Fintype.card F
  let m : ℝ := A.card
  let T : ℝ := m * q ^ (-δ)
  have hqpos : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hq1 : (1 : ℝ) ≤ q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hm_pos : 0 < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hqpos _) hA
  have hT_nonneg : 0 ≤ T := mul_nonneg hm_pos.le (Real.rpow_nonneg hqpos.le _)
  have hq_le_mr : q ≤ m ^ r := by
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hqpos.le _) hA r
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le] at hpow
    have hone : (1 / (r : ℝ)) * (r : ℝ) = 1 := by field_simp [hr_pos.ne']
    rw [hone, Real.rpow_one] at hpow
    exact hpow
  have hmom := exceptionalPoles_le hF A hb hT_nonneg hr
  have hterm1 : m ^ r * q ^ 2 ≤ m ^ (2 * r) * q := by
    calc m ^ r * q ^ 2 = (m ^ r * q) * q := by ring
      _ ≤ (m ^ r * m ^ r) * q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq_le_mr (by positivity)) hqpos.le
      _ = m ^ (2 * r) * q := by rw [← pow_add, show r + r = 2 * r by omega]
  have hrhs : (doubleFact r : ℝ) * m ^ r * q ^ 2 + (81 * (r : ℝ) ^ 2) * m ^ (2 * r) * q ≤
      ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) * (m ^ (2 * r) * q) := by
    have h1 : (doubleFact r : ℝ) * (m ^ r * q ^ 2) ≤ (doubleFact r : ℝ) * (m ^ (2 * r) * q) :=
      mul_le_mul_of_nonneg_left hterm1 (by positivity)
    linarith
  have hTpow : T ^ (2 * r) = m ^ (2 * r) * q ^ (-((2 * r : ℝ) * δ)) := by
    dsimp only [T]
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
    congr 1
    push_cast
    ring
  have hden_pos : 0 < m ^ (2 * r) * q ^ (η - (2 * r : ℝ) * δ) :=
    mul_pos (pow_pos hm_pos _) (Real.rpow_pos_of_pos hqpos _)
  have hden_le : m ^ (2 * r) * q ^ (η - (2 * r : ℝ) * δ) ≤ (b₀ : ℝ) * T ^ (2 * r) := by
    rw [hTpow, sub_eq_add_neg, Real.rpow_add hqpos]
    calc m ^ (2 * r) * (q ^ η * q ^ (-((2 * r : ℝ) * δ)))
        = q ^ η * (m ^ (2 * r) * q ^ (-((2 * r : ℝ) * δ))) := by ring
      _ ≤ (b₀ : ℝ) * (m ^ (2 * r) * q ^ (-((2 * r : ℝ) * δ))) :=
          mul_le_mul_of_nonneg_right hb_size (by positivity)
  have hN_mul : ((exceptionalPoles A b₀ T).card : ℝ) * (m ^ (2 * r) * q ^ (η - (2 * r : ℝ) * δ)) ≤
      ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) * (m ^ (2 * r) * q) :=
    (mul_le_mul_of_nonneg_left hden_le (Nat.cast_nonneg _)).trans (hmom.trans hrhs)
  apply le_of_mul_le_mul_right (a := m ^ (2 * r) * q ^ (η - (2 * r : ℝ) * δ)) _ hden_pos
  refine hN_mul.trans (le_of_eq ?_)
  have hqexp : q ^ (1 - η + (2 * r : ℝ) * δ) * q ^ (η - (2 * r : ℝ) * δ) = q := by
    rw [← Real.rpow_add hqpos]
    have hexp : 1 - η + (2 * r : ℝ) * δ + (η - (2 * r : ℝ) * δ) = 1 := by ring
    rw [hexp, Real.rpow_one]
  calc ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) * (m ^ (2 * r) * q)
      = ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) *
          (m ^ (2 * r) * (q ^ (1 - η + (2 * r : ℝ) * δ) * q ^ (η - (2 * r : ℝ) * δ))) := by
        rw [hqexp]
    _ = ((doubleFact r : ℝ) + 81 * (r : ℝ) ^ 2) * q ^ (1 - η + (2 * r : ℝ) * δ) *
          (m ^ (2 * r) * q ^ (η - (2 * r : ℝ) * δ)) := by ring

end ProximityGap.PaleyGramHigherMoment

#print axioms ProximityGap.PaleyGramHigherMoment.double_even_eq
#print axioms ProximityGap.PaleyGramHigherMoment.double_even_le
#print axioms ProximityGap.PaleyGramHigherMoment.chart_moment_le_gram
#print axioms ProximityGap.PaleyGramHigherMoment.partner_even_le
#print axioms ProximityGap.PaleyGramHigherMoment.exceptionalPoles_le
#print axioms ProximityGap.PaleyGramHigherMoment.exceptionalPoles_power_saving
