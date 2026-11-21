/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleySliceSampling
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp

/-!
# A single-cardinality test for prescribed quadratic discrepancy

Controlling the quadratic sum over each square of one given vertex cardinality controls
every difference rectangle with both sides at least that large.
-/

namespace ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic

open Finset PaleySliceSampling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def kernel (x y : F) : ℝ := quadraticChar F (x+y)
private def diag (x : F) : ℝ := kernel x x
private noncomputable def weight (F : Type*) [Fintype F] : ℝ := ((Fintype.card F : ℝ) - 2)⁻¹

private noncomputable def centered (x y : F) : ℝ :=
  kernel x y + weight F * (diag x + diag y) -
    if x = y then (1 + 2 * weight F) * diag x else 0

private theorem centered_symm (x y : F) : centered x y = centered y x := by
  by_cases h : x = y
  · rw [h]
  · simp [centered, h, Ne.symm h, kernel, add_comm]

private theorem centered_diag (x : F) : centered x x = 0 := by
  simp only [centered, ite_true, diag]
  ring

private theorem row_formula (x : F) (B : Finset F) :
    ∑ y ∈ B, centered x y = (∑ y ∈ B, kernel x y) +
      weight F * (B.card * diag x + ∑ y ∈ B, diag y) -
      if x ∈ B then (1 + 2 * weight F) * diag x else 0 := by
  simp only [centered, sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const,
    nsmul_eq_mul, sum_ite_eq]

private theorem cut_formula (A B : Finset F) :
    cutSum centered A B = cutSum kernel A B +
      weight F * (B.card * (∑ x ∈ A, diag x) + A.card * ∑ y ∈ B, diag y) -
        (1 + 2 * weight F) * ∑ x ∈ A ∩ B, diag x := by
  unfold cutSum
  simp_rw [row_formula]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
    sum_ite_mem]

private theorem row_zero (hF : ringChar F ≠ 2) (hN : 2 < Fintype.card F) (x : F) :
    ∑ y : F, centered x y = 0 := by
  have hsum : ∑ y : F, (quadraticChar F y : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hF
  have hk : ∑ y : F, kernel x y = 0 :=
    (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)).trans hsum
  have hd : ∑ y : F, diag y = 0 := by
    simp only [diag, kernel, ← two_mul, map_mul, Int.cast_mul, ← mul_sum, hsum, mul_zero]
  rw [row_formula, hk, hd]
  simp only [card_univ, add_zero, zero_add, mem_univ, ite_true, weight]
  have hq : (2 : ℝ) < Fintype.card F := by exact_mod_cast hN
  field_simp
  ring

private theorem abs_diag_sum (T : Finset F) : |∑ x ∈ T, diag x| ≤ T.card := calc
  _ ≤ _ := abs_sum_le_sum_abs _ _
  _ ≤ ∑ _ ∈ T, (1:ℝ) := by
    refine sum_le_sum fun x _ => ?_
    rcases (quadraticChar_isQuadratic F) (x+x) with h | h | h <;> simp [diag, kernel, h]
  _ = _ := by simp

omit [Field F] [DecidableEq F] in
private theorem scale_bounds {m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ Fintype.card F) :
    0 ≤ weight F ∧ 2 * weight F * (m+1 : ℝ) ≤ 1 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : (4 : ℝ)*m ≤ Fintype.card F := by exact_mod_cast hN
  have hden : (0 : ℝ) < Fintype.card F - 2 := by linarith
  constructor
  · exact inv_nonneg.mpr hden.le
  · change 2 * ((Fintype.card F : ℝ)-2)⁻¹ * (m + 1) ≤ 1
    rw [mul_right_comm, ← div_eq_mul_inv, div_le_iff₀ hden]
    linarith

private theorem fixed_square (D : ℝ) {m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ Fintype.card F)
    (h : ∀ S : Finset F, S.card = m → |pairSum kernel S| ≤ D)
    (T : Finset F) (hT : T.card = m) : |pairSum centered T| ≤ D + m := by
  obtain ⟨hw, hscale⟩ := scale_bounds hm hN
  let r := 2 * weight F * (m-1 : ℝ) - 1
  have hr : |r| ≤ 1 := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hpos : 0 ≤ weight F * (m-1 : ℝ) := mul_nonneg hw (by linarith)
    dsimp [r]
    rw [abs_le]
    constructor <;> nlinarith
  have hid : pairSum centered T = pairSum kernel T + r * ∑ x ∈ T, diag x := by
    change cutSum centered T T = cutSum kernel T T + _
    rw [cut_formula, inter_self, hT]
    dsimp [r]
    ring
  calc
    _ ≤ |pairSum kernel T| + |r| * |∑ x ∈ T, diag x| := by
      rw [hid, ← abs_mul]; exact abs_add_le _ _
    _ ≤ D + 1 * (T.card : ℝ) :=
      add_le_add (h T hT) (mul_le_mul hr (abs_diag_sum T) (abs_nonneg _) zero_le_one)
    _ = _ := by rw [one_mul, hT]

private theorem rectangle_error {m : ℕ} (hm : 2 ≤ m) (hN : 4*m ≤ Fintype.card F)
    (A B : Finset F) (hB : m ≤ B.card) :
    |cutSum kernel A B - cutSum centered A B| * m ≤ 2 * A.card * B.card := by
  obtain ⟨hw, hscale⟩ := scale_bounds hm hN
  let a : ℝ := A.card
  let b : ℝ := B.card
  let c : ℝ := (A ∩ B).card
  let w := weight F
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hb : (0:ℝ) ≤ b := Nat.cast_nonneg _
  have hmp : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hi : c * m ≤ a*b := by
    apply mul_le_mul _ _ hmp ha
    · dsimp [c,a]
      exact_mod_cast card_le_card (inter_subset_left (s₁ := A) (s₂ := B))
    · dsimp [b]
      exact_mod_cast hB
  have hnn : 0 ≤ 1+2*w := by dsimp [w]; linarith
  have hsum : |b*(∑ x ∈ A, diag x) + a*(∑ y ∈ B, diag y)| ≤ 2*(a*b) := calc
    _ ≤ |b*(∑ x ∈ A, diag x)| + |a*(∑ y ∈ B, diag y)| := abs_add_le _ _
    _ = b*|∑ x ∈ A, diag x| + a*|∑ y ∈ B, diag y| := by
      rw [abs_mul, abs_mul a, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ b*a + a*b := add_le_add (mul_le_mul_of_nonneg_left (abs_diag_sum A) hb)
      (mul_le_mul_of_nonneg_left (abs_diag_sum B) ha)
    _ = _ := by ring
  have hd : |cutSum kernel A B - cutSum centered A B| ≤ (1+2*w)*c + w*(2*(a*b)) := by
    rw [cut_formula, show ∀ x y z : ℝ, x-(x+y-z) = z-y by intros; ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hnn, abs_mul, abs_of_nonneg hw]
    exact add_le_add (mul_le_mul_of_nonneg_left (abs_diag_sum _) hnn)
      (mul_le_mul_of_nonneg_left hsum hw)
  calc
    _ ≤ ((1+2*w)*c + w*(2*(a*b)))*m := mul_le_mul_of_nonneg_right hd hmp
    _ = (1+2*w)*(c*m) + (2*w*m)*(a*b) := by ring
    _ ≤ (1+2*w)*(a*b) + (2*w*m)*(a*b) :=
      add_le_add (mul_le_mul_of_nonneg_left hi hnn) le_rfl
    _ = (1+2*w*(m+1))*(a*b) := by ring
    _ ≤ 2*(a*b) := mul_le_mul_of_nonneg_right (by linarith [hscale]) (mul_nonneg ha hb)
    _ = _ := by dsimp [a,b]; ring

/-- The tests on exactly `m` vertices give the stated absolute bound on every
prescribed sum rectangle whose sides have at least `m` vertices. -/
theorem sum_bound_of_one_size (hF : ringChar F ≠ 2) {m : ℕ} (hm : 2 ≤ m)
    (hN : 4*m ≤ Fintype.card F) {D : ℝ}
    (hsquare : ∀ T : Finset F, T.card = m →
      |∑ x ∈ T, ∑ y ∈ T, (quadraticChar F (x+y) : ℝ)| ≤ D)
    (A B : Finset F) (hA : m ≤ A.card) (hB : m ≤ B.card) :
    |∑ x ∈ A, ∑ y ∈ B, (quadraticChar F (x+y) : ℝ)| * (m : ℝ)^2 ≤
      (6*D + 8*m) * A.card * B.card := by
  have hw : 2 < Fintype.card F := by omega
  have hD : 0 ≤ D := by
    obtain ⟨T, hT⟩ := powersetCard_nonempty.mpr
      (show m ≤ (univ : Finset F).card by rw [card_univ]; omega)
    exact (abs_nonneg _).trans (hsquare T (mem_powersetCard.mp hT).2)
  have hc := cut_bound_of_one_size centered centered_diag centered_symm (row_zero hF hw) hm hN
    (add_nonneg hD (Nat.cast_nonneg m)) (fixed_square D hm hN hsquare) A B hA hB
  have he := rectangle_error hm hN A B hB
  have ha : |cutSum kernel A B| ≤
      |cutSum centered A B| + |cutSum kernel A B - cutSum centered A B| := by
    convert abs_add_le (cutSum centered A B) (cutSum kernel A B - cutSum centered A B) using 2
    ring
  calc
    _ ≤ (|cutSum centered A B| + |cutSum kernel A B - cutSum centered A B|) * (m:ℝ)^2 :=
      mul_le_mul_of_nonneg_right ha (sq_nonneg _)
    _ = |cutSum centered A B| * (m:ℝ)^2 +
        (|cutSum kernel A B - cutSum centered A B| * m) * m := by ring
    _ ≤ 6*(D+m)*A.card*B.card + (2*A.card*B.card)*m :=
      add_le_add hc (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
    _ = _ := by ring

/-- A one-cardinality quadratic sum test controls the relative discrepancy of every
prescribed difference rectangle, including overlapping sets. -/
theorem difference_bound_of_one_size (hF : ringChar F ≠ 2) {m : ℕ} (hm : 2 ≤ m)
    (hN : 4*m ≤ Fintype.card F) {D : ℝ}
    (hsquare : ∀ T : Finset F, T.card = m →
      |∑ x ∈ T, ∑ y ∈ T, (quadraticChar F (x+y) : ℝ)| ≤ D)
    (A B : Finset F) (hA : m ≤ A.card) (hB : m ≤ B.card) :
    |∑ x ∈ A, ∑ y ∈ B, (quadraticChar F (x-y) : ℝ)| / (A.card * B.card : ℝ) ≤
      6 * (D / (m : ℝ)^2) + 8/m := by
  let C := B.map (Equiv.neg F).toEmbedding
  have hC : C.card = B.card := card_map _
  have h := sum_bound_of_one_size hF hm hN hsquare A C hA (hC ▸ hB)
  simp only [C, sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, ← sub_eq_add_neg, card_map] at h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  have hb : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  apply (div_le_iff₀ (mul_pos ha hb)).mpr
  apply le_of_mul_le_mul_right (a := (m : ℝ)^2) _ (sq_pos_of_pos hm0)
  refine h.trans_eq ?_
  field_simp

/-- Number of ordered pairs in the rectangle whose difference is a nonzero square. -/
def edges (A B : Finset F) : ℕ :=
  ((A ×ˢ B).filter fun e => quadraticChar F (e.1 - e.2) = 1).card

/-- Doubled excess over half the off-diagonal ordered pairs is exactly the signed sum. -/
theorem edge_excess (A B : Finset F) :
    (2:ℝ) * (edges A B : ℝ) - (A.card * B.card : ℝ) + (A ∩ B).card =
      ∑ x ∈ A, ∑ y ∈ B, (quadraticChar F (x-y) : ℝ) := by
  classical
  have hpoint (x y : F) : (quadraticChar F (x-y) : ℝ) =
      2*(if quadraticChar F (x-y) = 1 then (1:ℝ) else 0) - 1 +
        (if x = y then 1 else 0) := by
    by_cases h : x = y
    · simp [h]
    · rcases quadraticChar_dichotomy (sub_ne_zero.mpr h) with h' | h' <;> norm_num [h', h]
  have hE : (edges A B : ℝ) =
      ∑ x ∈ A, ∑ y ∈ B, if quadraticChar F (x-y) = 1 then (1:ℝ) else 0 := by
    rw [edges, natCast_card_filter, sum_product]
  simp_rw [hpoint, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [← hE]
  simp [Finset.sum_ite_eq, sum_ite_mem, nsmul_eq_mul]

/-- The ordered Paley edge count compared with half the available ordered pairs.
At primes congruent to one modulo four this counts edges of the undirected Paley graph,
with both orientations present when both endpoints lie in the intersection. -/
theorem edge_bound_of_one_size (hF : ringChar F ≠ 2) {m : ℕ} (hm : 2 ≤ m)
    (hN : 4*m ≤ Fintype.card F) {D : ℝ}
    (hsquare : ∀ T : Finset F, T.card = m →
      |∑ x ∈ T, ∑ y ∈ T, (quadraticChar F (x+y) : ℝ)| ≤ D)
    (A B : Finset F) (hA : m ≤ A.card) (hB : m ≤ B.card) :
    |2 * (edges A B : ℝ) - (A.card * B.card : ℝ) + (A ∩ B).card| /
        (A.card * B.card : ℝ) ≤ 6*(D/(m:ℝ)^2) + 8/m := by
  rw [edge_excess]
  exact difference_bound_of_one_size hF hm hN hsquare A B hA hB

/-- Conversely, testing all prescribed equal-size difference rectangles includes every
square sum, by taking the second set to be the reflection of the first. -/
theorem square_test_of_difference {m : ℕ} {D : ℝ}
    (h : ∀ A B : Finset F, A.card = m → B.card = m →
      |∑ x ∈ A, ∑ y ∈ B, (quadraticChar F (x-y) : ℝ)| ≤ D)
    (T : Finset F) (hT : T.card = m) :
    |∑ x ∈ T, ∑ y ∈ T, (quadraticChar F (x+y) : ℝ)| ≤ D := by
  have hr := h T (T.map (Equiv.neg F).toEmbedding) hT (by rwa [card_map])
  simpa only [sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, sub_neg_eq_add] using hr

end ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic

#print axioms ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic.sum_bound_of_one_size
#print axioms ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic.difference_bound_of_one_size
#print axioms ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic.edge_bound_of_one_size

#print axioms ArkLib.ProximityGap.Frontier.PaleySingleSizeQuadratic.square_test_of_difference
