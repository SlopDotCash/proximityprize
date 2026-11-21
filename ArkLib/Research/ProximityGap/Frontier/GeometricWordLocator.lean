import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Error locators for a geometric-sum received word

The factorization with the domain polynomial follows by multiplying a residual by its
error locator. This file proves the degree and repeated-fibre steps that classify that
locator. The passage from the set of all Reed–Solomon candidates and the cyclotomic
argument for general shifted centers are in the research log.
-/

open Polynomial

namespace ProximityGap.GeometricWord

variable {F : Type*} [Field F]

/-- At the covering radius of the geometric-sum word, its monic error locator has
only an affine remainder after subtracting `X^h * (X - 1)`. -/
theorem locator_remainder_degree {k h : ℕ} (D P : F[X]) (hD : D.natDegree ≤ h + 1)
    (hP : P.natDegree < k)
    (hfactor : D * (X ^ (k + h) - 1 - (X - 1) * P) =
      (X ^ (k + h + h) - 1) * (X - 1)) :
    (D - X ^ h * (X - 1)).natDegree ≤ 1 := by
  let T : F[X] := D - X ^ h * (X - 1)
  change T.natDegree ≤ 1
  by_cases hT : T = 0
  · simp [hT]
  have hxp : (X - 1 : F[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hb : (1 + (X - 1) * P).natDegree ≤ k := by
    apply (natDegree_add_le _ _).trans
    refine max_le (by simp) (natDegree_mul_le.trans ?_)
    omega
  have hid : X ^ (k + h) * T = D * (1 + (X - 1) * P) - (X - 1) := by
    dsimp [T]
    rw [pow_add (X : F[X]) (k+h) h] at hfactor
    linear_combination hfactor
  have he : (X ^ (k+h) * T).natDegree ≤ k + h + 1 := by
    rw [hid]
    apply (natDegree_sub_le _ _).trans
    refine max_le (natDegree_mul_le.trans ?_) (hxp.trans (by omega))
    omega
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hT, natDegree_X_pow] at he
  omega

/-- Two locator roots with the same `h`-th power determine the affine remainder. -/
theorem locator_of_repeated_fibre {h : ℕ} (D : F[X])
    (hsmall : (D - X ^ h * (X - 1)).natDegree ≤ 1)
    {x y : F} (hxy : x ≠ y) (hsame : x ^ h = y ^ h)
    (hx : D.eval x = 0) (hy : D.eval y = 0) :
    D = (X ^ h - C (x ^ h)) * (X - 1) := by
  classical
  let R := D - (X ^ h - C (x ^ h)) * (X - 1)
  have hR : R.natDegree ≤ 1 := by
    have hr : R = (D - X ^ h * (X - 1)) + C (x ^ h) * (X - 1) := by dsimp [R]; ring
    rw [hr]
    refine (natDegree_add_le _ _).trans (max_le hsmall (natDegree_mul_le.trans ?_))
    have hd : (X - 1 : F[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    simpa using hd
  have hx' : R.eval x = 0 := by simp [R, hx]
  have hy' : R.eval y = 0 := by simp [R, hy, hsame]
  have rz : R = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero R (f := ((↑) : (↑({x,y} : Finset F) : Set F) → F)) Subtype.val_injective
    · rintro ⟨z, hz⟩
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx'
      · exact hy'
    · simpa [hxy] using (show R.natDegree < 2 by omega)
  exact sub_eq_zero.mp rz

/-- A geometric-sum locator with more distinct roots than available fibre values is
one full fibre together with the point `1`. -/
theorem geometric_locator_shape {k h : ℕ} (D P : F[X]) (hD : D.natDegree ≤ h + 1)
    (hP : P.natDegree < k)
    (hfactor : D * (X ^ (k + h) - 1 - (X - 1) * P) =
      (X ^ (k + h + h) - 1) * (X - 1))
    (errors fibres : Finset F) (hcount : fibres.card < errors.card)
    (hmap : ∀ x ∈ errors, x ^ h ∈ fibres) (hroot : ∀ x ∈ errors, D.eval x = 0) :
    ∃ t ∈ fibres, D = (X ^ h - C t) * (X - 1) := by
  classical
  obtain ⟨x,hx,y,hy,hne,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun z : F ↦ z ^ h) hcount hmap
  exact ⟨x ^ h, hmap x hx, locator_of_repeated_fibre D
    (locator_remainder_degree D P hD hP hfactor) hne he (hroot x hx) (hroot y hy)⟩

#print axioms geometric_locator_shape
end ProximityGap.GeometricWord
