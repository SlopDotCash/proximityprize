/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Four-cycle discrepancy on a prescribed bipartite Paley rectangle

The fourth power of discrepancy is bounded by the sum of the squared correlations
of pairs of columns. Multiplying rows or columns by signs preserves this energy.
A large energy requires large cut sums in the charts based at the specified columns.
-/

namespace ProximityGap.PaleyBipartiteCrossRatio

open Finset

variable {α β : Type*}

/-- Correlation of two columns over the supplied rows. -/
def gram (A : Finset α) (W : α → β → ℤ) (t b : β) : ℤ :=
  ∑ a ∈ A, W a t * W a b

/-- Signed four-cycle sum, expressed as the sum of squared column correlations. -/
def energy (A : Finset α) (B : Finset β) (W : α → β → ℤ) : ℤ :=
  ∑ t ∈ B, ∑ b ∈ B, (gram A W t b)^2

/-- The signed four-cycle sum equals its nonnegative Gram expression, including repeats. -/
theorem energy_eq_four_cycle (A : Finset α) (B : Finset β) (W : α → β → ℤ) :
    energy A B W =
      ∑ t ∈ B, ∑ b ∈ B, ∑ x ∈ A, ∑ y ∈ A, (W x t * W x b) * (W y t * W y b) := by
  simp only [energy, gram, pow_two, sum_mul_sum]

/-- A power saving in normalized four-cycle energy gives a fourth-root discrepancy saving. -/
theorem rectangle_fourth_le (A : Finset α) (B : Finset β) (W : α → β → ℤ) :
    (∑ a ∈ A, ∑ b ∈ B, W a b)^4 ≤ ((A.card : ℤ)*B.card)^2 * energy A B W := by
  classical
  let P := B ×ˢ B
  have hrows : (∑ a ∈ A, (∑ b ∈ B, W a b)^2) = ∑ u ∈ P, gram A W u.1 u.2 := by
    simp only [pow_two, sum_mul_sum, P, sum_product, gram]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun t _ => Finset.sum_comm
  have h1 : (∑ a ∈ A, ∑ b ∈ B, W a b)^2 ≤ A.card * ∑ u ∈ P, gram A W u.1 u.2 := by
    rw [← hrows]
    exact sq_sum_le_card_mul_sum_sq
  have h2 : (∑ u ∈ P, gram A W u.1 u.2)^2 ≤ (B.card : ℤ)^2 * energy A B W := by
    have h : (∑ u ∈ P, gram A W u.1 u.2)^2 ≤ P.card * ∑ u ∈ P, (gram A W u.1 u.2)^2 :=
      sq_sum_le_card_mul_sum_sq
    simpa only [P, card_product, Nat.cast_mul, sum_product, energy, pow_two] using h
  calc
    _ = ((∑ a ∈ A, ∑ b ∈ B, W a b)^2)^2 := by ring
    _ ≤ ((A.card : ℤ) * ∑ u ∈ P, gram A W u.1 u.2)^2 :=
      pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ ≤ (A.card : ℤ)^2 * ((B.card : ℤ)^2 * energy A B W) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

/-- Row and column interchange preserves the four-cycle count. -/
theorem energy_transpose (A : Finset α) (B : Finset β) (W : α → β → ℤ) :
    energy A B W = energy B A (fun t x => W x t) := by
  rw [energy_eq_four_cycle, energy_eq_four_cycle]
  have h := Finset.sum_comm (s := B ×ˢ B) (t := A ×ˢ A)
    (f := fun t x => (W x.1 t.1 * W x.1 t.2) * (W x.2 t.1 * W x.2 t.2))
  simp only [sum_product] at h
  rw [h]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ =>
    sum_congr rfl fun t _ => sum_congr rfl fun b _ => ?_
  ring

private theorem energy_mono_right (A : Finset α) {B D : Finset β} (h : B ⊆ D)
    (W : α → β → ℤ) : energy A B W ≤ energy A D W := by
  calc
    _ ≤ ∑ t ∈ B, ∑ y ∈ D, (gram A W t y)^2 := by
      apply sum_le_sum
      exact fun t _ => sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

/-- Separate monotonicity lets one ambient principal set control all its subrectangles. -/
theorem energy_mono {A C : Finset α} {B D : Finset β} (ha : A ⊆ C) (hb : B ⊆ D)
    (W : α → β → ℤ) : energy A B W ≤ energy C D W := by
  apply (energy_mono_right A hb W).trans
  rw [energy_transpose A D, energy_transpose C D]
  exact energy_mono_right D ha _

/-- Row and column sign changes, including projective changes of homogeneous lifts,
preserve the energy of each supplied rectangle. -/
theorem energy_signs (A : Finset α) (B : Finset β) (W : α → β → ℤ)
    (u : α → ℤ) (v : β → ℤ) (hu : ∀ a ∈ A, u a ^ 2 = 1) (hv : ∀ b ∈ B, v b ^ 2 = 1) :
    energy A B (fun a b => u a * v b * W a b) = energy A B W := by
  have hrow (t b : β) :
      gram A (fun a b => u a * v b * W a b) t b = (v t * v b) * gram A W t b := by
    unfold gram
    rw [mul_sum]
    refine sum_congr rfl fun a ha => ?_
    calc
      _ = u a ^ 2 * ((v t*v b) * (W a t*W a b)) := by ring
      _ = _ := by rw [hu a ha, one_mul]
  unfold energy
  refine sum_congr rfl fun t ht => sum_congr rfl fun b hb => ?_
  rw [hrow, mul_pow, mul_pow, hv t ht, hv b hb, one_mul, one_mul]

/-- A signed four-cycle with nonzero denominator is the character of its cross-ratio. -/
theorem quadratic_cross_ratio {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x y t b : F)
    (h : (x-b)*(y-t) ≠ 0) :
    (quadraticChar F (x-t)*quadraticChar F (x-b)) *
        (quadraticChar F (y-t)*quadraticChar F (y-b)) =
      quadraticChar F (((x-t)*(y-b))/((x-b)*(y-t))) := by
  let n := (x-t)*(y-b)
  let d := (x-b)*(y-t)
  have hd : quadraticChar F d ^ 2 = 1 := quadraticChar_sq_one h
  have hmul : quadraticChar F (n/d) * quadraticChar F d = quadraticChar F n := by
    rw [← map_mul, div_mul_cancel₀ n h]
  calc
    _ = quadraticChar F n * quadraticChar F d := by simp only [n, d, map_mul]; ring
    _ = (quadraticChar F (n/d) * quadraticChar F d) * quadraticChar F d := by rw [hmul]
    _ = _ := by rw [mul_assoc, ← pow_two, hd, mul_one]

private theorem mass_le_twice_cut (B : Finset β) (f : β → ℤ) (R : ℤ)
    (hR : ∀ Y ⊆ B, |∑ b ∈ Y, f b| ≤ R) :
    ∑ b ∈ B, |f b| ≤ 2*R := by
  classical
  let P := B.filter (fun b => 0 ≤ f b)
  let N := B.filter (fun b => ¬ 0 ≤ f b)
  have hp := abs_le.mp (hR P (filter_subset ..))
  have hn := abs_le.mp (hR N (filter_subset ..))
  have hsplit : ∑ b ∈ B, |f b| = (∑ b ∈ P, f b) - ∑ b ∈ N, f b := by
    simp only [P, N, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    by_cases h : 0 ≤ f b <;> simp [h, abs_of_nonneg, abs_of_neg, lt_of_not_ge]
  omega

/-- Average local cuts at the designated target poles control the four-cycle sum.
At each pole any orientation of the off-diagonal Gram entries preserving magnitude is valid. -/
theorem energy_le_local_cuts [DecidableEq β] (A : Finset α) (B : Finset β)
    (W : α → β → ℤ) (hw : ∀ a ∈ A, ∀ b ∈ B, |W a b| ≤ 1)
    (f : β → β → ℤ) (R : β → ℤ)
    (hf : ∀ t ∈ B, ∀ b ∈ B.erase t, |f t b| = |gram A W t b|)
    (hR : ∀ t ∈ B, ∀ Y ⊆ B.erase t, |∑ b ∈ Y, f t b| ≤ R t) :
    energy A B W ≤ (A.card : ℤ)^2 * B.card + 2*A.card*∑ t ∈ B, R t := by
  have hG (t : β) (ht : t ∈ B) (b : β) (hb : b ∈ B) :
      |gram A W t b| ≤ (A.card : ℤ) := by
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _a ∈ A, (1 : ℤ) := by
        apply sum_le_sum
        intro a ha
        rw [abs_mul]
        simpa using mul_le_mul (hw a ha t ht) (hw a ha b hb) (abs_nonneg _) (by decide)
      _ = _ := by simp
  have hrow (t : β) (ht : t ∈ B) :
      ∑ b ∈ B, (gram A W t b)^2 ≤ (A.card : ℤ)^2 + 2*A.card*R t := by
    have hm := mass_le_twice_cut (B.erase t) (f t) (R t) (hR t ht)
    rw [← sum_erase_add _ _ ht]
    have hd : (gram A W t t)^2 ≤ (A.card : ℤ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hG t ht t ht) 2
    have ho : ∑ b ∈ B.erase t, (gram A W t b)^2 ≤ (A.card : ℤ)*(2*R t) := calc
      _ ≤ ∑ b ∈ B.erase t, (A.card:ℤ)*|f t b| := by
        refine sum_le_sum fun b hb => ?_
        rw [hf t ht b hb, ← sq_abs, pow_two]
        exact mul_le_mul_of_nonneg_right (hG t ht b (mem_of_mem_erase hb)) (abs_nonneg _)
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hm (by positivity)
    linarith
  calc
    _ ≤ ∑ t ∈ B, ((A.card : ℤ)^2 + 2*A.card*R t) := sum_le_sum hrow
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp [mul_comm]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem char_div (x d : F) (hd : d ≠ 0) :
    quadraticChar F (x/d) = quadraticChar F x * quadraticChar F d := by
  have h : quadraticChar F (x/d) * quadraticChar F d = quadraticChar F x := by
    rw [← map_mul, div_mul_cancel₀ x hd]
  rw [← h, mul_assoc, ← pow_two, quadraticChar_sq_one hd, mul_one]

/-- Unweighted row after inversion of the prescribed source, with its pole removed. -/
def inverseRow (A : Finset F) (t b : F) : ℤ :=
  ∑ x ∈ A.erase t, quadraticChar F ((x-t)⁻¹-(b-t)⁻¹)

/-- Away from the pole the absolute inverted row is exactly the Gram entry. -/
theorem abs_inverseRow (A : Finset F) (t b : F) (hb : b ≠ t) :
    |inverseRow A t b| = |gram A (fun x y => quadraticChar F (x-y)) t b| := by
  let c := quadraticChar F (-1) * quadraticChar F (b-t)
  have hbt := sub_ne_zero.mpr hb
  have hc : |c| = 1 := by
    dsimp only [c]
    rw [abs_mul]
    rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0)) with h|h <;>
      rcases quadraticChar_dichotomy hbt with h'|h' <;> rw [h,h'] <;> decide
  have ht : inverseRow A t b = c * gram A (fun x y => quadraticChar F (x-y)) t b := by
    let w (x : F) := quadraticChar F (x-t)*quadraticChar F (x-b)
    have herase : ∑ x ∈ A.erase t, w x = ∑ x ∈ A, w x := by
      by_cases h : t ∈ A
      · simpa [w] using sum_erase_add A w h
      · rw [erase_eq_of_notMem h]
    change (∑ x ∈ A.erase t, _) = c * ∑ x ∈ A, w x
    rw [← herase, mul_sum]
    refine sum_congr rfl fun x hx => ?_
    have hxt := sub_ne_zero.mpr (ne_of_mem_erase hx)
    have hd : (x-t)⁻¹-(b-t)⁻¹ = (b-x)/((x-t)*(b-t)) := by field_simp; ring
    rw [hd, char_div _ _ (mul_ne_zero hxt hbt), show b-x=(-1)*(x-b) by ring]
    simp only [c, w, map_mul]
    ring
  rw [ht, abs_mul, hc, one_mul]

/-- A bound for cuts following inversion at the prescribed partner poles suffices for
the original cycle energy. The source undergoes no adaptive sign restriction. -/
theorem paley_energy_le_inverse_cuts (A B : Finset F) (R : F → ℤ)
    (hR : ∀ t ∈ B, ∀ Y ⊆ B.erase t, |∑ b ∈ Y, inverseRow A t b| ≤ R t) :
    energy A B (fun x y => quadraticChar F (x-y)) ≤
      (A.card : ℤ)^2 * B.card + 2*A.card*∑ t ∈ B, R t := by
  apply energy_le_local_cuts A B _ _ (inverseRow A) R _ hR
  · intro a _ b _
    by_cases h : a-b=0
    · simp [h]
    · rcases quadraticChar_dichotomy h with h'|h' <;> rw [h'] <;> decide
  · exact fun t _ b hb => abs_inverseRow A t b (ne_of_mem_erase hb)

/-- Integral four-site matrix with sign ratio `e` under reversal of a directed edge. -/
def fourSiteMatrix (e a b c d f g : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,a,b,c; e*a,0,d,f; e*b,e*d,0,g; e*c,e*f,e*g,0]

private theorem det_expanded (e a b c d f g : ℤ) :
    (fourSiteMatrix e a b c d f g).det =
      e^2*(a^2*g^2+b^2*f^2+c^2*d^2) - (e+e^3)*(a*c*d*g) -
      2*e^2*(a*b*f*g+b*c*d*f) := by
  rw [Matrix.det_succ_row_zero]
  simp [fourSiteMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

private theorem sign_cases (z : ℤ) (hz : z^2 = 1) : z = 1 ∨ z = -1 := by
  have h : (z-1)*(z+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h|h <;> omega

/-- The integer determinant is determined by two Hamilton cycle signs. -/
theorem four_site_det (e a b c d f g : ℤ) (he : e^2=1) (ha : a^2=1) (hb : b^2=1)
    (hc : c^2=1) (hd : d^2=1) (hf : f^2=1) (hg : g^2=1) :
    (fourSiteMatrix e a b c d f g).det =
      3-2*((e*a*c*d*g)+(a*b*f*g)+e*(e*a*c*d*g)*(a*b*f*g)) := by
  have he3 : e^3=e := by rw [pow_succ, he, one_mul]
  rw [det_expanded, he3, he, ha, hb, hc, hd, hf, hg]
  have hw : e*(e*a*c*d*g)*(a*b*f*g) = b*c*d*f := calc
    _ = e^2*a^2*g^2*(b*c*d*f) := by ring
    _ = _ := by rw [he,ha,hg]; ring
  rw [hw]
  ring

/-- Singularity modulo three detects precisely the four-site type with both cycle
signs equal to the reversal sign. This holds in the symmetric and skew cases. -/
theorem four_site_singular_mod_three (e a b c d f g : ℤ) (he : e^2=1) (ha : a^2=1)
    (hb : b^2=1) (hc : c^2=1) (hd : d^2=1) (hf : f^2=1) (hg : g^2=1) :
    (((fourSiteMatrix e a b c d f g).det : ℤ) : ZMod 3) = 0 ↔
      (e*a*c*d*g = e ∧ a*b*f*g = e) := by
  rw [four_site_det e a b c d f g he ha hb hc hd hf hg]
  let u := e*a*c*d*g
  let v := a*b*f*g
  have hu : u^2=1 := by simp [u,mul_pow,he,ha,hc,hd,hg]
  have hv : v^2=1 := by simp [v,mul_pow,ha,hb,hf,hg]
  change ((3-2*(u+v+e*u*v) : ℤ) : ZMod 3) = 0 ↔ u=e ∧ v=e
  rcases sign_cases e he with E|E <;> rcases sign_cases u hu with U|U <;>
    rcases sign_cases v hv with V|V <;> rw [U,V,E] <;> decide

end ProximityGap.PaleyBipartiteCrossRatio

#print axioms ProximityGap.PaleyBipartiteCrossRatio.rectangle_fourth_le
#print axioms ProximityGap.PaleyBipartiteCrossRatio.quadratic_cross_ratio
#print axioms ProximityGap.PaleyBipartiteCrossRatio.energy_signs
#print axioms ProximityGap.PaleyBipartiteCrossRatio.energy_le_local_cuts

#print axioms ProximityGap.PaleyBipartiteCrossRatio.paley_energy_le_inverse_cuts

#print axioms ProximityGap.PaleyBipartiteCrossRatio.energy_mono
#print axioms ProximityGap.PaleyBipartiteCrossRatio.four_site_singular_mod_three
