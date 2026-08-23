/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BinomialMatrixDet
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# The classical (Hasse) Wronskian of distinct-degree monomials is nonzero (#389)

For naturals `m₀, …, m_{l-1}` distinct in a field `F`, the **classical Hasse-Wronskian determinant**

  `W := det[ hasseDeriv a (X^{mⱼ}) ]_{a,j}`

is nonzero (`hasseWronskian_monomial_ne_zero`). The proof reads off the coefficient at degree
`D = ∑mⱼ − l(l−1)/2`: since `hasseDeriv a (X^{mⱼ}) = C(mⱼ,a)·X^{mⱼ−a}`, every permutation term of the
determinant is a monomial of the *same* degree `D`, so `W.coeff D = det[C(mᵢ,a)]` — the binomial
determinant, which is nonzero by `det_choose_ne_zero` when the `mᵢ` are distinct in `F`.

## Role in #389

This is the *classical* (derivative) analogue of the already-proven *folded* (dilation) Wronskian
non-vanishing `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent`. The classical
Wronskian is the non-vanishing tool used by the Shkredov–Vyugin / Heath-Brown–Konyagin additive-shift
Stepanov argument that bounds `|R ∩ (R+μ)|` (hence the additive energy `E(μ_n)`, hence the sub-Johnson
list-size / supply wall). This file supplies its monomial core; the remaining layers toward
`GVRepBound` are: distinct-degree *polynomials* (leading-monomial term = this), general independent
families (via `GK16Finish.exists_distinctDegree_recombination`), and the SV11 multiplicity-on-`V`
construction.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Product of monomials is the monomial of summed exponents and multiplied coefficients. -/
lemma prod_monomial {ι : Type*} (s : Finset ι) (k : ι → ℕ) (c : ι → F) :
    ∏ i ∈ s, (monomial (k i) (c i) : F[X]) = monomial (∑ i ∈ s, k i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, Finset.prod_insert ha,
        monomial_mul_monomial]

/-- The `D`-th coefficient of `∏ᵢ C(mᵢ,σᵢ)·X^{mᵢ−σᵢ}` is `∏ᵢ C(mᵢ,σᵢ)`, where `D = ∑mⱼ − ∑positions`:
either some `C(mᵢ,σᵢ) = 0` (both sides vanish) or all `mᵢ ≥ σᵢ` and the product has degree exactly
`D`. -/
lemma coeff_D_prod {l : ℕ} (m : Fin l → ℕ) (σ : Equiv.Perm (Fin l)) :
    (∏ i : Fin l, (monomial (m i - σ i) (↑(Nat.choose (m i) (σ i)) : F))).coeff
        ((∑ j, m j) - ∑ a : Fin l, (a : ℕ))
      = ∏ i : Fin l, (↑(Nat.choose (m i) (σ i)) : F) := by
  rw [prod_monomial, coeff_monomial]
  by_cases hprod : (∏ i : Fin l, (↑(Nat.choose (m i) (σ i)) : F)) = 0
  · rw [hprod]; simp
  · have hall : ∀ i, (σ i : ℕ) ≤ m i := by
      intro i
      by_contra h
      push_neg at h
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]))
    have hsum : (∑ i : Fin l, (m i - σ i)) = (∑ j, m j) - ∑ a : Fin l, (a : ℕ) := by
      rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hall i)]
      congr 1
      exact Equiv.sum_comp σ (fun a => (a : ℕ))
    rw [if_pos hsum]

/-- **The classical (Hasse) Wronskian of distinct-degree monomials is nonzero.** For naturals `mⱼ`
distinct in `F` (`i ↦ (mⱼ : F)` injective), `det[ hasseDeriv a (X^{mⱼ}) ]_{a,j} ≠ 0`. -/
theorem hasseWronskian_monomial_ne_zero {l : ℕ} (m : Fin l → ℕ)
    (hinj : Function.Injective (fun i => (m i : F))) :
    (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) ((X : F[X]) ^ (m j)))).det ≠ 0 := by
  classical
  set D := (∑ j, m j) - ∑ a : Fin l, (a : ℕ) with hD
  -- Step 1: the `D`-th coefficient of the Wronskian det equals `det[C(m y, x)]`.
  have step1 : (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) ((X : F[X]) ^ (m j)))).det.coeff D
      = (Matrix.of (fun x y : Fin l => (Nat.choose (m y) x : F))).det := by
    rw [Matrix.det_apply', Polynomial.finset_sum_coeff, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Polynomial.coeff_intCast_mul]
    congr 1
    have hentry : ∀ i, (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) ((X : F[X]) ^ (m j))))
        (σ i) i = monomial (m i - σ i) (↑(Nat.choose (m i) (σ i)) : F) := by
      intro i
      simp only [Matrix.of_apply]
      rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one]
    rw [Finset.prod_congr rfl (fun i _ => hentry i), coeff_D_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [Matrix.of_apply]
  -- Step 2: relate to the binomial determinant via transpose, then `det_choose_ne_zero`.
  have hcoeff : (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) ((X : F[X]) ^ (m j)))).det.coeff D
      = (Matrix.of (fun i a : Fin l => (Nat.choose (m i) a : F))).det := by
    rw [step1]
    have htr : (Matrix.of (fun x y : Fin l => (Nat.choose (m y) x : F)))
        = (Matrix.of (fun i a : Fin l => (Nat.choose (m i) a : F)))ᵀ := by
      ext x y; simp [Matrix.transpose_apply, Matrix.of_apply]
    rw [htr, Matrix.det_transpose]
  intro hzero
  apply det_choose_ne_zero m hinj
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.hasseWronskian_monomial_ne_zero
