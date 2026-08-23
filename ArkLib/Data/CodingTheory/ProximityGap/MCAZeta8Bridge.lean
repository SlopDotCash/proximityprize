/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAVerticalStratumCharZero
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The `ℤ[ζ₈]` coordinate bridge (#357 round 12): census-by-computation foundation

The slanted-stratum completeness question at a fixed smooth scale (`n = 8`: are the 40
classified circuits *all* of them, in char 0?) reduces to deciding, per pair-triangle,
whether an explicit element of `ℤ[ζ₈]` vanishes. Writing the collinearity determinant in
the power basis `det = c₀ + c₁ζ + c₂ζ² + c₃ζ³` (integer coordinates, computable by
reducing powers via `ζ⁴ = −1`), vanishing is decided by the **coordinate bridge**:

* **`zeta8_linear_independence`** — over any `CharZero` field, an integer combination
  `c₀ + c₁ζ + c₂ζ² + c₃ζ³ = 0` at a primitive 8th root forces all four coordinates to
  vanish: a nonzero integer cubic at `ζ` would be divisible by the degree-4 minimal
  polynomial `Φ₈ = X⁴ + 1`.

Consequence: a `μ₈` pair-triangle is a wide circuit in *some* char-0 field iff in
*every* char-0 field iff its integer coordinate vector vanishes — the complete `n = 8`
census becomes a finite integer computation against the landed pencil criterion, and the
same bridge (power basis + minpoly degree) scales to every `μ_{2^k}` with
`Φ_{2^k} = X^{2^{k−1}} + 1`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-11 close); `LamLeungTwoPow.lean` (the minpoly-divisibility pattern).
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace ProximityGap.MCAZeta8Bridge

variable {L : Type*} [Field L] [CharZero L]

/-- **The coordinate bridge.** Over a `CharZero` field, integer combinations of
`1, ζ, ζ², ζ³` at a primitive 8th root vanish only trivially. -/
theorem zeta8_linear_independence {ζ : L} (hζ : IsPrimitiveRoot ζ 8)
    {c₀ c₁ c₂ c₃ : ℤ}
    (h : (c₀ : L) + (c₁ : L) * ζ + (c₂ : L) * ζ ^ 2 + (c₃ : L) * ζ ^ 3 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  set p : ℚ[X] := C (c₀ : ℚ) + C (c₁ : ℚ) * X + C (c₂ : ℚ) * X ^ 2
    + C (c₃ : ℚ) * X ^ 3 with hp
  have halg : ∀ q : ℚ, algebraMap ℚ L q = (q : L) := fun q =>
    eq_ratCast (algebraMap ℚ L) q
  -- ζ annihilates p
  have haev : Polynomial.aeval ζ p = 0 := by
    rw [hp]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [halg, halg, halg, halg]
    push_cast
    exact h
  -- p must be zero: otherwise the degree-4 minimal polynomial divides a cubic
  have hple : p.natDegree ≤ 3 := by
    rw [hp]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (le_of_eq (Polynomial.natDegree_C _)) (by norm_num)
        · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
            (le_trans Polynomial.natDegree_X_le (by norm_num))
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
          (le_of_eq (Polynomial.natDegree_X_pow 2) |>.trans (by norm_num))
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_of_eq (Polynomial.natDegree_X_pow 3))
  have hp0 : p = 0 := by
    by_contra hpne
    have hdvd := minpoly.dvd ℚ ζ haev
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by norm_num : 0 < 8)] at hdvd
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hpne
    have hcyc : (Polynomial.cyclotomic 8 ℚ).natDegree = 4 := by
      rw [Polynomial.natDegree_cyclotomic]
      decide
    omega
  -- extract coefficients
  have hc : ∀ k : ℕ, p.coeff k = 0 := by
    intro k
    rw [hp0]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hc 0
    rw [hp] at this
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at this
    norm_num at this
    exact_mod_cast this
  · have := hc 1
    rw [hp] at this
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at this
    norm_num at this
    exact_mod_cast this
  · have := hc 2
    rw [hp] at this
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at this
    norm_num at this
    exact_mod_cast this
  · have := hc 3
    rw [hp] at this
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at this
    norm_num at this
    exact_mod_cast this

/-! ## Source audit -/

#print axioms zeta8_linear_independence

end ProximityGap.MCAZeta8Bridge
