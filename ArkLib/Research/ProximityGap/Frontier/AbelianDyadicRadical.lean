/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # The fourth root of two and abelian extensions of the rationals

The conjugate of the square of a real fourth root would be a negative square.
The argument uses only the quadratic minimal polynomial.
-/

namespace ProximityGap.AbelianDyadicRadical

open Polynomial

private theorem sqrt_two_minpoly {E : Type*} [Field E] [Algebra ℚ E]
    (y : E) (hy : y^2 = 2) : minpoly ℚ y = X^2 - C 2 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    have h : IsSquare ((2 : ℕ) : ℚ) := ⟨b, by norm_num [pow_two] at hb ⊢; exact hb.symm⟩
    have hn := Rat.isSquare_natCast_iff.mp h
    obtain ⟨s,hs⟩ := hn
    rcases le_or_gt s 1 with h | h
    · interval_cases s <;> contradiction
    · nlinarith
  · simpa using sub_eq_zero.mpr hy
  · exact monic_X_pow_sub_C _ (by decide)

/-- An ordered normal extension of the rationals has no fourth root of two. -/
theorem fourth_power_ne_two {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    [Algebra ℚ E] [Normal ℚ E] (x : E) : x^4 ≠ 2 := by
  intro h
  have hs : (x^2)^2 = 2 := by simpa only [← pow_mul] using h
  have hm := sqrt_two_minpoly (x^2) hs
  have hr : (aeval (-(x^2))) (minpoly ℚ (x^2)) = 0 := by
    rw [hm]
    simpa using sub_eq_zero.mpr hs
  obtain ⟨σ,hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic (R:=ℚ) _) hr
  rw [map_pow] at hσ
  have hp : 0 < x^2 := sq_pos_of_ne_zero (by intro hz; simp [hz] at h)
  nlinarith [sq_nonneg (σ x)]

/-- No ordered field containing a fourth root of two can embed over the rationals
in an abelian Galois extension, finite or infinite. -/
theorem no_abelian_embedding {E K : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    [Field K] [Algebra ℚ E] [Algebra ℚ K] [IsAbelianGalois ℚ K]
    (x : E) (hx : x^4 = 2) (f : E →ₐ[ℚ] K) : False := by
  have := IsAbelianGalois.of_algHom f
  exact fourth_power_ne_two x hx

/-- An abelian subfield of the complex numbers omits every real fourth root of two. -/
theorem real_fourth_root_not_mem (K : IntermediateField ℚ ℂ) [IsAbelianGalois ℚ K]
    (x : ℝ) (hx : x^4 = 2) : (x : ℂ) ∉ K := by
  intro h
  let f : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  let E := K.comap f
  let : IsStrictOrderedRing E := Function.Injective.isStrictOrderedRing (Subtype.val : E → ℝ)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) .rfl .rfl
  let y : E := ⟨x,h⟩
  have hy : y^4 = 2 := Subtype.ext hx
  let g : E →ₐ[ℚ] K := (f.comp E.val).codRestrict K.toSubalgebra (fun z ↦ z.property)
  exact no_abelian_embedding y hy g

#print axioms real_fourth_root_not_mem
#print axioms fourth_power_ne_two
#print axioms no_abelian_embedding

end ProximityGap.AbelianDyadicRadical
