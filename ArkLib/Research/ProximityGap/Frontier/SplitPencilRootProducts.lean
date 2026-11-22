/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! # Root products and reflection distances of split pencils -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset

namespace ProximityGap.SplitPencilRootProducts
variable {F : Type*} [Field F]

private theorem locator_zero (S : Finset F) :
    (∏ a ∈ S, (X - C a)).eval 0 = (-1 : F) ^ S.card * ∏ a ∈ S, a := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, ih, pow_succ]; ring

/-- The common - degree factors of the pencil obey the same affine relation at the level of
their root products. -/
theorem product_relation (A B D : Finset F) (hAB : A.card = B.card) (hAD : A.card = D.card)
    (c : F) (h : (∏ a ∈ A, (X - C a)) - C c * (∏ b ∈ B, (X - C b)) =
      C (1 - c) * (∏ d ∈ D, (X - C d))) :
    (∏ a ∈ A, a) - c * (∏ b ∈ B, b) = (1 - c) * ∏ d ∈ D, d := by
  have he := congrArg (Polynomial.eval 0) h
  simp only [eval_sub, eval_mul, eval_C, locator_zero, ← hAB, ← hAD] at he
  apply mul_left_cancel₀ (pow_ne_zero A.card (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)))
  linear_combination he

/-- Products are either all equal or pairwise different, and in the latter case the
pencil coefficient is the ratio of two differences of products. -/
theorem chord_or_equal {a b d c : F} (hc : c ≠ 0) (hc' : c ≠ 1)
    (h : a - c * b = (1 - c) * d) :
    (a = d ∧ b = d) ∨ (a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c = (a - d) / (b - d)) := by
  have he : a - d = c * (b - d) := by linear_combination h
  by_cases hb : b = d
  · exact Or.inl ⟨sub_eq_zero.mp (by simpa [hb] using he), hb⟩
  · refine Or.inr ⟨?_, ?_, hb, (eq_div_iff (sub_ne_zero.mpr hb)).mpr he.symm⟩
    · intro hab
      apply hc'
      apply mul_right_cancel₀ (sub_ne_zero.mpr hb)
      simpa [hab] using he.symm
    · exact sub_ne_zero.mp (he ▸ mul_ne_zero hc (sub_ne_zero.mpr hb))

/-- The ratio corrected by the chord at a center has value one, and the same correction
makes the products of its numerator and denominator roots equal. -/
theorem corrected_center {a b d c x u v : F} (hd : d ≠ 0)
    (h : a - c * b = (1 - c) * d) (hu : u = c * v) :
    u * (x - x * b / d) = v * (x - x * a / d) ∧ a * (x * b / d) = b * (x * a / d) := by
  subst u
  constructor <;> field_simp
  · linear_combination v * x * h

private def scaled (r : F) (A : F[X]) := A.comp (C r * X)

private theorem scaled_degree {m : ℕ} (r : F) (A : F[X]) (ha : A.natDegree ≤ m) :
    (scaled r A).natDegree ≤ m := by
  calc
    _ ≤ A.natDegree * (C r * X).natDegree := natDegree_comp_le
    _ ≤ m * 1 := Nat.mul_le_mul ha (natDegree_C_mul_le r X |>.trans (by simp))
    _ = _ := by simp

private def mirror (m : ℕ) (r : F) (A : F[X]) := reflect m (scaled r A)

private theorem mirror_degree {m : ℕ} (r : F) (A : F[X]) (ha : A.natDegree ≤ m) :
    (mirror m r A).natDegree ≤ m :=
  natDegree_reflect_le.trans (max_le le_rfl (scaled_degree r A ha))

private theorem mirror_eval {m : ℕ} (r : F) (A : F[X]) (ha : A.natDegree ≤ m)
    {x : F} (hx : x ≠ 0) : (mirror m r A).eval x = A.eval (r / x) * x ^ m := by
  let _ : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have he := eval₂_reflect_mul_pow (RingHom.id F) x⁻¹ m (scaled r A) (scaled_degree r A ha)
  simp only [invOf_eq_inv, inv_inv, eval₂_id, inv_pow] at he
  rw [← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hx)] at he
  simpa [mirror, scaled, eval_comp, div_eq_mul_inv] using he

/-- A non - invariant monic rational pencil can agree with its mirror on at most twice its
degree many nonzero sites. Equal constant coefficients save two further sites. Include
every available mirror fixed point in the tested set. -/
theorem mirror_site_bound {m : ℕ} (A B : F[X]) (r : F)
    (ha : A.natDegree ≤ m) (hb : B.natDegree ≤ m) (ha' : A.coeff m = 1) (hb' : B.coeff m = 1)
    (S : Finset F) (hs : 0 ∉ S)
    (hmatch : ∀ x ∈ S, A.eval (r / x) * B.eval x = B.eval (r / x) * A.eval x)
    (hmoved : ∃ x : F, x ≠ 0 ∧ A.eval (r / x) * B.eval x ≠ B.eval (r / x) * A.eval x) :
    S.card ≤ 2 * m ∧ (A.eval 0 = B.eval 0 → S.card + 2 ≤ 2 * m) := by
  classical
  let Q := mirror m r A * B - mirror m r B * A
  have hma := mirror_degree r A ha
  have hmb := mirror_degree r B hb
  have hdeg : Q.natDegree ≤ m + m := (natDegree_sub_le ..).trans
    (max_le (natDegree_mul_le.trans (Nat.add_le_add hma hb))
      (natDegree_mul_le.trans (Nat.add_le_add hmb ha)))
  have hev (x : F) (hx : x ≠ 0) :
      Q.eval x = (A.eval (r / x) * B.eval x - B.eval (r / x) * A.eval x) * x ^ m := by
    simp only [Q, eval_sub, eval_mul, mirror_eval r A ha hx, mirror_eval r B hb hx]
    ring
  have hz (x : F) (hx : x ∈ S) : Q.eval x = 0 := by
    rw [hev x (fun h => hs (h ▸ hx)), hmatch x hx, sub_self, zero_mul]
  have hQ : Q ≠ 0 := by
    obtain ⟨x, hx, ht⟩ := hmoved
    intro he
    have hh := hev x hx
    rw [he, eval_zero] at hh
    exact mul_ne_zero (sub_ne_zero.mpr ht) (pow_ne_zero _ hx) hh.symm
  constructor
  · by_contra! h
    exact hQ (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q S hz (by omega))
  intro heq
  have htop : Q.coeff (m + m) = 0 := by
    dsimp only [Q]
    rw [coeff_sub, coeff_mul_add_eq_of_natDegree_le hma hb, coeff_mul_add_eq_of_natDegree_le hmb ha]
    simp [mirror, scaled, coeff_reflect, revAt_le, ha', hb', coeff_zero_eq_eval_zero, heq]
  have hdeg' : Q.natDegree < m + m := lt_of_le_of_ne hdeg (fun h =>
    leadingCoeff_ne_zero.mpr hQ (by simpa [leadingCoeff, h] using htop))
  have hzero : Q.eval 0 = 0 := by
    simp [Q, mirror, scaled, ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le,
      ha', hb', ← coeff_zero_eq_eval_zero A, ← coeff_zero_eq_eval_zero B] at heq ⊢
    simp [heq]
  by_contra! h
  apply hQ
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q (insert 0 S) _ (by
    rw [card_insert_of_notMem hs]
    omega)
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hzero
  · exact hz x hx

end ProximityGap.SplitPencilRootProducts
