/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPolynomial
import ArkLib.Data.CodingTheory.GMMDS.LovettSubstitutionDvd
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456

/-!
# Lovett's GM-MDS proof: the merge substitution identity (#389)

The algebraic heart of the merge branch of Lovett's Lemma 2.5 (arXiv:1803.02523, p.9): under the
variable substitution `a_last ↦ a_{j*}` the two vanishing factors `(x − a_{j*})^{v(j*)}` and
`(x − a_last)^{v(last)}` collapse into a single factor `(x − a_{j*})^{v(j*) + v(last)}` of summed
multiplicity.  Equivalently, applying the coefficient-lifted substitution
`substVarP last j* := Polynomial.mapAlgHom (substVar last j*)` to `pVanish v` produces `pVanish`
of the *collapsed* multiplicity vector

> `collapseVec j* v := v` with the `last` coordinate zeroed and its value added onto `j*`.

This is the identity that, fed into the substitution-divisibility kernel
`sub_X_dvd_of_subst_eq_zero`, drives the contradiction in the merge branch.

## Results

* `collapseVec` — `v` with `last` merged into `j*`.
* `substVarP` — the coefficient-lifted substitution on `(MvPolynomial (Fin n) F)[X]`.
* `substVarP_xSubA` — `substVarP last j* (x − a_c) = x − a_{(c = last ? j* : c)}`.
* `substVarP_pVanish` — `substVarP last j* (pVanish v) = pVanish (collapseVec j* v)` (the core
  collapse identity).
* `substVarP_pFam` — the same lifted to the shifted family `pFam` (`X^e` is fixed by the
  substitution).

Issue #389.
-/

open Polynomial Finset MvPolynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- `v` with the last coordinate merged into `j`: zero out `last`, add its value onto `j`. -/
noncomputable def collapseVec {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (v : Fin n → ℕ) : Fin n → ℕ :=
  fun c => if c = lastCoord n hn then 0
           else if c = j then v j + v (lastCoord n hn)
           else v c

/-- The coefficient-lifted substitution `a_last ↦ a_j` on `(MvPolynomial (Fin n) F)[X]`. -/
noncomputable def substVarP (F : Type*) [Field F] {n : ℕ} (j l : Fin n) :
    (MvPolynomial (Fin n) F)[X] →ₐ[F] (MvPolynomial (Fin n) F)[X] :=
  Polynomial.mapAlgHom (substVar (F := F) l j)

@[simp] theorem substVarP_X {n : ℕ} (j l : Fin n) :
    substVarP F j l Polynomial.X = Polynomial.X := by
  simp [substVarP]

theorem substVarP_C {n : ℕ} (j l : Fin n) (a : MvPolynomial (Fin n) F) :
    substVarP F j l (Polynomial.C a) = Polynomial.C (substVar (F := F) l j a) := by
  simp [substVarP]

/-- The image of a linear factor `x − a_c` under the substitution `a_last ↦ a_j`. -/
theorem substVarP_xSubA {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (c : Fin n) :
    substVarP F j (lastCoord n hn) (xSubA c)
      = xSubA (if c = lastCoord n hn then j else c) := by
  unfold xSubA
  rw [map_sub, substVarP_X, substVarP_C]
  congr 1
  by_cases h : c = lastCoord n hn
  · rw [if_pos h, h, substVar_X_self]
  · rw [if_neg h, substVar_X_of_ne h]

/-- **The merge collapse identity.**  Substituting `a_last ↦ a_j` collapses the two vanishing
factors `(x − a_j)^{v(j)}` and `(x − a_last)^{v(last)}` into one of summed multiplicity:
`substVarP last↦j (pVanish v) = pVanish (collapseVec j v)`. -/
theorem substVarP_pVanish {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (hjlt : j ≠ lastCoord n hn)
    (v : Fin n → ℕ) :
    substVarP F j (lastCoord n hn) (pVanish v) = pVanish (collapseVec hn j v) := by
  classical
  set l := lastCoord n hn with hldef
  -- LHS: apply the hom to the product
  rw [pVanish, map_prod]
  have hLHS : ∀ c, substVarP F j l ((xSubA c) ^ (v c))
      = (xSubA (if c = l then j else c)) ^ (v c) := by
    intro c; rw [map_pow, substVarP_xSubA hn j c]
  rw [Finset.prod_congr rfl (fun c _ => hLHS c)]
  -- Both sides: split off {j, l} from univ.
  have hsub : ({j, l} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  -- RHS
  rw [pVanish]
  rw [← Finset.prod_sdiff hsub, ← Finset.prod_sdiff (s₁ := ({j, l} : Finset (Fin n))) hsub]
  congr 1
  · -- on the complement, the index map is the identity and collapseVec = v
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hc
    obtain ⟨-, hc2⟩ := hc
    push_neg at hc2
    obtain ⟨hcj, hcl⟩ := hc2
    rw [if_neg hcl]
    congr 1
    unfold collapseVec
    rw [if_neg (hldef ▸ hcl), if_neg hcj]
  · -- on {j, l}: LHS = (xSubA j)^{v j} * (xSubA j)^{v l}; RHS = (xSubA j)^{v j + v l} * 1
    rw [Finset.prod_pair hjlt, Finset.prod_pair hjlt]
    rw [if_neg hjlt, if_pos rfl]
    have hcollj : collapseVec hn j v j = v j + v l := by
      unfold collapseVec; rw [if_neg hjlt, if_pos rfl]
    have hcolll : collapseVec hn j v l = 0 := by
      unfold collapseVec; rw [if_pos rfl]
    rw [hcollj, hcolll, pow_add, pow_zero, mul_one]

/-- The merge collapse identity lifted to the shifted family `pFam` (`X^e` is fixed). -/
theorem substVarP_pFam {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (hjlt : j ≠ lastCoord n hn)
    (v : Fin n → ℕ) (e : ℕ) :
    substVarP F j (lastCoord n hn) (pFam v e) = pFam (collapseVec hn j v) e := by
  unfold pFam
  rw [map_mul, substVarP_pVanish hn j hjlt, map_pow, substVarP_X]

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.substVarP_xSubA
#print axioms ArkLib.GMMDS.substVarP_pVanish
#print axioms ArkLib.GMMDS.substVarP_pFam
