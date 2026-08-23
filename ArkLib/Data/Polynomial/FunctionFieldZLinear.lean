/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Polynomial.RationalFunctionsCore

/-!
# Linear independence of `{1, T}` in the function field `𝕃 H`

We work in the function field `𝕃 H = (RatFunc F)[Y] ⧸ (H_tilde H)` defined in
`ArkLib.Data.Polynomial.RationalFunctionsCore`, where `H_tilde H` is the monicization of a
bivariate polynomial `H : F[X][Y]` (Appendix A.1 of [BCIKS20]).

The embedding `liftToFunctionField : F[X] →+* 𝕃 H` sends a coefficient polynomial `c` to the
class of the constant polynomial `C (univPolyHom c)`, and `functionFieldT : 𝕃 H` is the class of
the variable `Y` (the adjoined root `T`).

When `H.natDegree ≥ 2`, the defining relation `H_tilde H` has `Y`-degree `≥ 2`, so the classes of
`1` and `Y` are `RatFunc F`-linearly independent. Concretely, the only way a degree-`< 2`
polynomial `C a + Y * C b` can vanish in the quotient is if it is the zero polynomial. This gives:

* `liftToFunctionField_add_T_mul_eq_zero_iff` (core independence): the combination
  `liftToFunctionField c₀ + functionFieldT * liftToFunctionField c₁` vanishes iff `c₀ = c₁ = 0`.
* `functionFieldT_lift_independent`: the forward direction, packaged for direct use.
* `liftToFunctionField_T_repr_unique` (uniqueness): the `{1, T}`-representation of an element by
  `F[X]`-coefficients is unique.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. FOCS 2020. https://eprint.iacr.org/2020/654.
-/

set_option linter.style.longLine false

noncomputable section

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

variable {F : Type} [Field F]

/-- The univariate coefficient embedding `F[X] → RatFunc F` is injective. (The corresponding
lemma in `RationalFunctionsCore` is `private`, so we restate it here from the Mathlib fact for
`algebraMap`.) -/
private lemma univPolyHom_injective' :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

section TIndependence

variable {H : F[X][Y]}

/-- The combination `liftToFunctionField c₀ + functionFieldT * liftToFunctionField c₁` is the class
in `𝕃 H` of the explicit degree-`≤ 1` polynomial `C (univPolyHom c₀) + X * C (univPolyHom c₁)`. -/
private lemma liftToFunctionField_add_T_mul_eq_mk (c₀ c₁ : F[X]) :
    liftToFunctionField (H := H) c₀ + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ =
      Ideal.Quotient.mk (Ideal.span {H_tilde H})
        (Polynomial.C (univPolyHom (F := F) c₀) +
          Polynomial.X * Polynomial.C (univPolyHom (F := F) c₁)) := by
  have h₀ : liftToFunctionField (H := H) c₀ =
      Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.C (univPolyHom (F := F) c₀)) := by
    rw [liftToFunctionField, RingHom.comp_apply, coeffAsRatFunc_eq_C]
  have h₁ : liftToFunctionField (H := H) c₁ =
      Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.C (univPolyHom (F := F) c₁)) := by
    rw [liftToFunctionField, RingHom.comp_apply, coeffAsRatFunc_eq_C]
  have hT : functionFieldT (H := H) =
      Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.X : Polynomial (RatFunc F)) := rfl
  rw [h₀, h₁, hT, ← map_mul, ← map_add]

/-- **Core `{1, T}` linear independence in `𝕃 H`.**

When `H.natDegree ≥ 2`, the only `F[X]`-coefficient combination of `1` and the adjoined root
`functionFieldT` that vanishes in the function field is the trivial one. -/
theorem liftToFunctionField_add_T_mul_eq_zero_iff
    [Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hdeg : 2 ≤ H.natDegree) (c₀ c₁ : F[X]) :
    liftToFunctionField (H := H) c₀ + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ = 0
      ↔ c₀ = 0 ∧ c₁ = 0 := by
  classical
  -- The explicit representative polynomial of the combination.
  set P : Polynomial (RatFunc F) :=
    Polynomial.C (univPolyHom (F := F) c₀) + Polynomial.X * Polynomial.C (univPolyHom (F := F) c₁)
    with hP_def
  have hg_monic : (H_tilde H).Monic := H_tilde_monic (H := H) H_natDegree_pos.out
  -- The combination is the class of `P`.
  rw [liftToFunctionField_add_T_mul_eq_mk (H := H) c₀ c₁, ← hP_def]
  -- The class of `P` vanishes iff `H_tilde H ∣ P` iff `P %ₘ (H_tilde H) = 0`.
  -- Build this equivalence at the value level to avoid a dependent-type motive failure.
  have h_iff :
      (Ideal.Quotient.mk (Ideal.span {H_tilde H}) P = 0) ↔ P %ₘ (H_tilde H) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton).trans
      (Polynomial.modByMonic_eq_zero_iff_dvd hg_monic).symm
  rw [h_iff]
  -- The degree of `H_tilde H` is `H.natDegree ≥ 2`.
  have hg_deg : (H_tilde H).degree = (H.natDegree : WithBot ℕ) := by
    rw [degree_H_tilde_eq (H := H) H_natDegree_pos.out,
      Polynomial.degree_eq_natDegree (H_tilde'_monic H H_natDegree_pos.out).ne_zero,
      natDegree_H_tilde' (H := H) H_natDegree_pos.out]
  -- `P` has degree `≤ 1 < H.natDegree`, so `P %ₘ (H_tilde H) = P`.
  have hP_deg : P.degree < (H_tilde H).degree := by
    rw [hg_deg]
    refine lt_of_le_of_lt (b := (1 : WithBot ℕ)) ?_ ?_
    · refine (Polynomial.degree_add_le _ _).trans ?_
      refine max_le ?_ ?_
      · exact (Polynomial.degree_C_le).trans (by decide)
      · refine (Polynomial.degree_mul_le _ _).trans ?_
        have hX : (Polynomial.X : Polynomial (RatFunc F)).degree ≤ 1 := Polynomial.degree_X_le
        have hC : (Polynomial.C (univPolyHom (F := F) c₁)).degree ≤ 0 := Polynomial.degree_C_le
        calc (Polynomial.X : Polynomial (RatFunc F)).degree +
              (Polynomial.C (univPolyHom (F := F) c₁)).degree
            ≤ (1 : WithBot ℕ) + 0 := add_le_add hX hC
          _ = 1 := by simp
    · exact_mod_cast hdeg
  have hP_mod : P %ₘ (H_tilde H) = P := (Polynomial.modByMonic_eq_self_iff hg_monic).2 hP_deg
  rw [hP_mod]
  -- Now `P = 0 ↔ c₀ = 0 ∧ c₁ = 0`: extract coefficients `0` and `1`.
  constructor
  · intro hP0
    have hc₀ : univPolyHom (F := F) c₀ = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 0) hP0
      simpa [hP_def, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul] using this
    have hc₁ : univPolyHom (F := F) c₁ = 0 := by
      have := congrArg (fun q => Polynomial.coeff q 1) hP0
      simpa [hP_def, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_zero] using this
    refine ⟨?_, ?_⟩
    · have := univPolyHom_injective' (F := F) (a₁ := c₀) (a₂ := 0) (by simpa using hc₀)
      simpa using this
    · have := univPolyHom_injective' (F := F) (a₁ := c₁) (a₂ := 0) (by simpa using hc₁)
      simpa using this
  · rintro ⟨rfl, rfl⟩
    simp [hP_def]

/-- The forward direction of `{1, T}` independence: if the `F[X]`-coefficient combination of `1`
and `functionFieldT` vanishes in `𝕃 H` then both coefficients are zero. -/
theorem functionFieldT_lift_independent
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdeg : 2 ≤ H.natDegree) {c₀ c₁ : F[X]}
    (h : liftToFunctionField (H := H) c₀ +
        functionFieldT (H := H) * liftToFunctionField (H := H) c₁ = 0) :
    c₀ = 0 ∧ c₁ = 0 :=
  (liftToFunctionField_add_T_mul_eq_zero_iff (H := H) hdeg c₀ c₁).1 h

end TIndependence

section Uniqueness

variable {H : F[X][Y]}

/-- **Uniqueness of the `{1, T}`-representation.**

If two `F[X]`-coefficient combinations of `1` and `functionFieldT` agree in `𝕃 H`, then their
coefficients agree. This is the uniqueness statement for the `Z`-linear (here `F[X]`-linear)
representation by `1` and `T`. -/
theorem liftToFunctionField_T_repr_unique
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdeg : 2 ≤ H.natDegree) {a₀ a₁ b₀ b₁ : F[X]}
    (h : liftToFunctionField (H := H) a₀ + functionFieldT (H := H) * liftToFunctionField (H := H) a₁
        = liftToFunctionField (H := H) b₀ +
            functionFieldT (H := H) * liftToFunctionField (H := H) b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  -- Move everything to one side: `lift (a₀ - b₀) + T * lift (a₁ - b₁) = 0`.
  have hzero :
      liftToFunctionField (H := H) (a₀ - b₀) +
        functionFieldT (H := H) * liftToFunctionField (H := H) (a₁ - b₁) = 0 := by
    have h₀ := (liftToFunctionField (H := H)).map_sub a₀ b₀
    have h₁ := (liftToFunctionField (H := H)).map_sub a₁ b₁
    rw [h₀, h₁, mul_sub]
    rw [sub_add_sub_comm, h, sub_self]
  obtain ⟨hd₀, hd₁⟩ :=
    functionFieldT_lift_independent (H := H) hdeg hzero
  refine ⟨?_, ?_⟩
  · exact sub_eq_zero.1 hd₀
  · exact sub_eq_zero.1 hd₁

end Uniqueness

end BCIKS20AppendixA

end

#print axioms BCIKS20AppendixA.liftToFunctionField_add_T_mul_eq_zero_iff
#print axioms BCIKS20AppendixA.functionFieldT_lift_independent
#print axioms BCIKS20AppendixA.liftToFunctionField_T_repr_unique
