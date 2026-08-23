/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Linearized (q-additive) polynomial kernel

Kernel identities underlying linearized / q-additive polynomials and BKR06 subspace
polynomials, not currently in mathlib. For a finite field `F` with `q = |F|`:

* `prod_X_sub_C_univ_eq_pow_card_sub` — base-field subspace polynomial:
  `∏_{c ∈ F} (X - C c) = X^q - X`.
* `prod_X_sub_C_algebraMap_eq_pow_card_sub` — its image in an extension `K`:
  `∏_{c ∈ F} (X - C (ι c)) = X^q - X` in `K[X]`.
* `prod_X_sub_C_smul_eq` — the **scaled linearized kernel**: for `a ≠ 0` in `K`,
  `∏_{c ∈ F} (X - C (a · ι c)) = X^q - C (a^{q-1}) · X`.

These feed the q-linearized-support recursion used by the BKR06 list-size argument.
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {F : Type*} [Field F] [Fintype F]

/-- **Base-field subspace polynomial.** Over a finite field `F` with `q = |F|`,
`∏_{c ∈ F} (X - C c) = X^q - X`. -/
theorem prod_X_sub_C_univ_eq_pow_card_sub :
    (∏ c : F, (X - C c)) = X ^ (Fintype.card F) - X := by
  classical
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hmonic : (X ^ Fintype.card F - X : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hsplits : Splits (X ^ Fintype.card F - X : F[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, ← Finset.card_def, Finset.card_univ]
  have hprod := hsplits.eq_prod_roots_of_monic hmonic
  rw [FiniteField.roots_X_pow_card_sub_X] at hprod
  rw [hprod]
  rfl

variable {K : Type*} [Field K] [Algebra F K]

/-- **Base-field subspace polynomial in an extension.** Mapping
`prod_X_sub_C_univ_eq_pow_card_sub` through `algebraMap F K`:
`∏_{c ∈ F} (X - C (ι c)) = X^q - X` in `K[X]`. -/
theorem prod_X_sub_C_algebraMap_eq_pow_card_sub :
    (∏ c : F, (X - C (algebraMap F K c))) = X ^ (Fintype.card F) - X := by
  have h := congrArg (Polynomial.map (algebraMap F K)) (prod_X_sub_C_univ_eq_pow_card_sub (F := F))
  simpa only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_pow] using h

/-- **Linearized kernel.** For `a ≠ 0` in an extension `K` of the finite field `F` (`q = |F|`),
`∏_{c ∈ F} (X - C (a · ι c)) = X^q - C (a^{q-1}) · X`.

Proof: factor `C a` out of each linear factor, reducing the product to a `comp` of the base-field
identity by `C a⁻¹ · X`; evaluate `(X^q - X).comp (C a⁻¹ X) = C(a⁻¹^q) X^q - C a⁻¹ X`; multiply by
`(C a)^q = C(a^q)` and simplify the scalars using `a^q a⁻¹^q = 1` and `a^q a⁻¹ = a^{q-1}`. -/
theorem prod_X_sub_C_smul_eq (a : K) (ha : a ≠ 0) :
    (∏ c : F, (X - C (a * algebraMap F K c)))
      = X ^ (Fintype.card F) - C (a ^ (Fintype.card F - 1)) * X := by
  classical
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hCaa : C a * C a⁻¹ = (1 : K[X]) := by rw [← C_mul, mul_inv_cancel₀ ha, C_1]
  have hfactor : ∀ c : F, X - C (a * algebraMap F K c)
      = C a * (C a⁻¹ * X - C (algebraMap F K c)) := fun c => by
    rw [mul_sub, ← mul_assoc, hCaa, one_mul, ← C_mul]
  rw [Finset.prod_congr rfl (fun c _ => hfactor c), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  -- inner product = comp of the base-field identity by `C a⁻¹ * X`
  have hcomp : (∏ c : F, (C a⁻¹ * X - C (algebraMap F K c)))
      = Polynomial.comp (X ^ Fintype.card F - X) (C a⁻¹ * X) := by
    rw [← prod_X_sub_C_algebraMap_eq_pow_card_sub (F := F) (K := K), Polynomial.prod_comp]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [sub_comp, X_comp, C_comp]
  rw [hcomp, sub_comp, pow_comp, X_comp, mul_pow]
  simp only [← C_pow]
  have e1 : a ^ Fintype.card F * a⁻¹ ^ Fintype.card F = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  have e2 : a ^ Fintype.card F * a⁻¹ = a ^ (Fintype.card F - 1) := by
    conv_lhs => rw [show Fintype.card F = (Fintype.card F - 1) + 1 from by omega, pow_succ]
    rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
  rw [mul_sub, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, e1, e2, C_1, one_mul]

/-- **Polynomial-generalized linearized kernel (recursion engine).** For any polynomial `P : K[X]`
and `a ≠ 0`, `∏_{c ∈ F} (P - C (a · ι c)) = P^q - C (a^{q-1}) · P`.

This is `prod_X_sub_C_smul_eq` composed with `P` (substitute `X ↦ P`); it is the exact step of the
q-linearized subspace-polynomial recursion, with `P = s_{V'}` and `a = s_{V'}(u)`:
`s_{V'⊕F·u} = ∏_{c∈F} (s_{V'} - c · s_{V'}(u)) = s_{V'}^q - s_{V'}(u)^{q-1} · s_{V'}`. -/
theorem prod_sub_C_smul_eq (P : K[X]) (a : K) (ha : a ≠ 0) :
    (∏ c : F, (P - C (a * algebraMap F K c)))
      = P ^ (Fintype.card F) - C (a ^ (Fintype.card F - 1)) * P := by
  have hstep : (∏ c : F, (P - C (a * algebraMap F K c)))
      = (∏ c : F, (X - C (a * algebraMap F K c))).comp P := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [sub_comp, X_comp, C_comp]
  rw [hstep, prod_X_sub_C_smul_eq a ha, sub_comp, pow_comp, X_comp, mul_comp, C_comp, X_comp]

end ArkLib.LinearizedKernel

-- Axiom audit: each result must rest only on `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.LinearizedKernel.prod_X_sub_C_univ_eq_pow_card_sub
#print axioms ArkLib.LinearizedKernel.prod_X_sub_C_algebraMap_eq_pow_card_sub
#print axioms ArkLib.LinearizedKernel.prod_X_sub_C_smul_eq
#print axioms ArkLib.LinearizedKernel.prod_sub_C_smul_eq
