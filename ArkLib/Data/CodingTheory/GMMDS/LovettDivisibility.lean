/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPolynomial
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparation

/-!
# Lovett's GM-MDS proof: the `(x − aⱼ)`-divisibility dichotomy (#389)

Concrete inputs to the separation engine ([[LovettSeparation]]).  For Lovett's family element
`pFam v e = (∏ⱼ (x − aⱼ)^{v(j)})·xᵉ` (arXiv:1803.02523):

* `v(j) ≥ 1 ⟹ (x − aⱼ) ∣ pFam v e`   — the reduced family `P(k,V')` is all divisible by the
  distinguished factor.
* `v(j) = 0 ⟹ ¬ (x − aⱼ) ∣ pFam v e`  — the separated polynomial is not, because evaluating at
  `aⱼ = X j` gives `∏ₗ (X j − X l)^{v(l)} · (X j)ᵉ ≠ 0` (every factor is a nonzero difference of
  distinct variables, in the integral domain `MvPolynomial (Fin n) F`).

Combined with `linearIndependent_option_of_dvd` these discharge the closing contradiction and
the leaf steps of Lemmas 2.5/2.6.

Issue #389.
-/

open Polynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- If `v(j) ≥ 1` then `(x − aⱼ)` divides the vanishing polynomial. -/
theorem xSubA_dvd_pVanish {v : Fin n → ℕ} {j : Fin n} (hj : 1 ≤ v j) :
    xSubA (F := F) j ∣ pVanish (F := F) v :=
  Dvd.intro _ (pVanish_factor hj).symm

/-- If `v(j) ≥ 1` then `(x − aⱼ)` divides the family element `pFam v e`. -/
theorem xSubA_dvd_pFam {v : Fin n → ℕ} {j : Fin n} (hj : 1 ≤ v j) (e : ℕ) :
    xSubA (F := F) j ∣ pFam (F := F) v e :=
  Dvd.dvd.mul_right (xSubA_dvd_pVanish hj) _

/-- Evaluating `pVanish v` at `aⱼ = X j` gives the product of difference-powers. -/
theorem eval_Xj_pVanish (v : Fin n → ℕ) (j : Fin n) :
    (pVanish (F := F) v).eval (MvPolynomial.X j)
      = ∏ l, (MvPolynomial.X j - MvPolynomial.X l) ^ (v l) := by
  rw [pVanish, eval_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [eval_pow, xSubA, eval_sub, eval_X, eval_C]

/-- If `v(j) = 0` then `pVanish v` does not vanish at `aⱼ = X j` (distinct variables differ). -/
theorem eval_Xj_pVanish_ne_zero {v : Fin n → ℕ} {j : Fin n} (hvj : v j = 0) :
    (pVanish (F := F) v).eval (MvPolynomial.X j) ≠ 0 := by
  rw [eval_Xj_pVanish]
  refine Finset.prod_ne_zero_iff.mpr (fun l _ => ?_)
  rcases Nat.eq_zero_or_pos (v l) with h0 | hpos
  · rw [h0, pow_zero]; exact one_ne_zero
  · refine pow_ne_zero _ (sub_ne_zero.mpr (fun hX => ?_))
    have hjl : j = l := MvPolynomial.X_injective hX
    rw [← hjl, hvj] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- If `v(j) = 0` then `(x − aⱼ)` does not divide `pFam v e`. -/
theorem not_xSubA_dvd_pFam {v : Fin n → ℕ} {j : Fin n} (hvj : v j = 0) (e : ℕ) :
    ¬ xSubA (F := F) j ∣ pFam (F := F) v e := by
  intro hdvd
  have hroot := eval_eq_zero_of_dvd (c := MvPolynomial.X j) (q := pFam (F := F) v e) (by
    simpa [xSubA] using hdvd)
  rw [pFam, eval_mul, eval_pow, eval_X] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · exact eval_Xj_pVanish_ne_zero hvj h
  · exact (pow_ne_zero _ (MvPolynomial.X_ne_zero j)) h

end ArkLib.GMMDS

#print axioms ArkLib.GMMDS.xSubA_dvd_pFam
#print axioms ArkLib.GMMDS.not_xSubA_dvd_pFam
