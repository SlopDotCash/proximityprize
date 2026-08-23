/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCombinatorial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic

/-!
# Lovett's GM-MDS proof: the polynomial framework (#389, layer 2)

The algebraic side of Lovett (arXiv:1803.02523), in `F[a][x]` (univariate `x` over
`F[a] = MvPolynomial (Fin n) F`).  For `v : Fin n → ℕ`,
`pVanish v = ∏ⱼ (x − aⱼ)^{v(j)}` (monic, degree `|v|`), `pFam v e = pVanish v · xᵉ`.
Lovett's `P(k,v) = { pFam v e : e < k−|v| }`; Theorem 1.7 = linear independence of
`⋃ᵢ P(k,vᵢ)` over `F(a)`.

* `pVanish_monic`, `pVanish_natDegree`, `pFam_natDegree`.
* `pVanish_factor` (Lemmas 2.2/2.4 core): `v(j) ≥ 1 ⟹ pVanish v = (x−aⱼ)·pVanish(v−eⱼ)`.

Issue #389.
-/

open Polynomial Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear factor `x − aⱼ` in `F[a][x]`. -/
noncomputable def xSubA (j : Fin n) : (MvPolynomial (Fin n) F)[X] :=
  Polynomial.X - Polynomial.C (MvPolynomial.X j)

theorem xSubA_monic (j : Fin n) : (xSubA (F := F) j).Monic := monic_X_sub_C _

theorem xSubA_natDegree (j : Fin n) : (xSubA (F := F) j).natDegree = 1 :=
  natDegree_X_sub_C _

/-- The vanishing polynomial `∏ⱼ (x − aⱼ)^{v(j)}`. -/
noncomputable def pVanish (v : Fin n → ℕ) : (MvPolynomial (Fin n) F)[X] :=
  ∏ j, (xSubA j) ^ (v j)

theorem pVanish_monic (v : Fin n → ℕ) : (pVanish (F := F) v).Monic :=
  monic_prod_of_monic _ _ (fun j _ => (xSubA_monic j).pow _)

theorem pVanish_natDegree (v : Fin n → ℕ) :
    (pVanish (F := F) v).natDegree = vAbs v := by
  classical
  rw [pVanish, natDegree_prod_of_monic _ _ (fun j _ => (xSubA_monic j).pow _), vAbs]
  exact Finset.sum_congr rfl (fun j _ => by rw [natDegree_pow, xSubA_natDegree, mul_one])

/-- The shifted family element `pVanish v · xᵉ`. -/
noncomputable def pFam (v : Fin n → ℕ) (e : ℕ) : (MvPolynomial (Fin n) F)[X] :=
  pVanish v * Polynomial.X ^ e

theorem pFam_natDegree (v : Fin n → ℕ) (e : ℕ) :
    (pFam (F := F) v e).natDegree = vAbs v + e := by
  rw [pFam, natDegree_mul (pVanish_monic v).ne_zero (pow_ne_zero e X_ne_zero),
    pVanish_natDegree, natDegree_X_pow]

/-- **The coordinate-peeling factorization** (Lovett, core of Lemmas 2.2/2.4): if
`v(j) ≥ 1`, the vanishing polynomial factors out one `(x − aⱼ)`. -/
theorem pVanish_factor {v : Fin n → ℕ} {j : Fin n} (hj : 1 ≤ v j) :
    pVanish (F := F) v = xSubA j * pVanish (Function.update v j (v j - 1)) := by
  classical
  set w : Fin n → ℕ := Function.update v j (v j - 1) with hw
  have hexp : ∀ i, v i = w i + (if i = j then 1 else 0) := by
    intro i
    by_cases h : i = j
    · subst h; rw [hw, Function.update_self, if_pos rfl]; omega
    · rw [hw, Function.update_of_ne h, if_neg h]; omega
  calc pVanish v
      = ∏ i, (xSubA (F := F) i) ^ (w i + (if i = j then 1 else 0)) := by
        rw [pVanish]; exact Finset.prod_congr rfl (fun i _ => by rw [hexp i])
    _ = (∏ i, (xSubA (F := F) i) ^ (w i)) * ∏ i, (xSubA (F := F) i) ^ (if i = j then 1 else 0) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun i _ => by rw [pow_add])
    _ = pVanish w * xSubA j := by
        rw [pVanish]
        congr 1
        rw [Finset.prod_eq_single j (fun i _ hi => by rw [if_neg hi, pow_zero])
          (fun h => absurd (Finset.mem_univ j) h), if_pos rfl, pow_one]
    _ = xSubA j * pVanish w := by rw [mul_comm]

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.pVanish_natDegree
#print axioms ArkLib.GMMDS.pVanish_factor
