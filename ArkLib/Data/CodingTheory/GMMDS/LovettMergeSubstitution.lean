/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettPolynomial
import ArkLib.Data.CodingTheory.GMMDS.LovettSubstitutionDvd

/-!
# Lovett's GM-MDS proof: the merge-substitution transport bricks (Lemma 2.6) (#389)

The remaining TRUE residual of Lovett's Theorem 1.7 is `LovettMergeIndep` (the prize route R3):
a *primitive* `V*(k)` system containing a merge candidate `(i₀, j*)` (with `V i₀ j* = 0`,
`j* < n−1`, `V i₀ (n−1) = 0`) is linearly independent.  Lovett's proof (Lemma 2.6, arXiv:1803.02523
p.9) substitutes `a_{n−1} ↦ a_{j*}`, collapsing the system to a smaller one handled by the
induction hypotheses, then uses the substitution-divisibility kernel
(`LovettSubstitutionDvd.sub_X_dvd_of_subst_eq_zero`) plus a minimal-counterexample contradiction.

This file formalizes the **transport machinery** for that argument — the lifted substitution
`substPoly p q = Polynomial.map (substVar p q)` on `R[X]` (`R = MvPolynomial (Fin n) F`) and how it
interacts with the vanishing polynomials `pVanish`, working **in fixed dimension `n`** (the merge is
realized as `mergeVec p q`, which moves the `p`-mass onto `q` and zeroes `p`, keeping the variable
set `Fin n`; the reindexing `Fin n → Fin (n−1)` needed to invoke the `n`-IH, and the final
minimality contradiction, are NOT in this file — see the residual note below).

## Results (all axiom-clean: `propext`, `Classical.choice`, `Quot.sound` only)

* `substPoly`, `substPoly_X`, `substPoly_C`, `substPoly_xSubC`, `substPoly_xSubA` — the lifted
  substitution and its action on `X`, `C`, and the linear factors `xSubA i`.
* `mergeVec`, `vAbs_mergeVec` — **(S1 core)** the merged multiplicity vector and weight
  preservation `|mergeVec p q v| = |v|` (`p ≠ q`).
* `substPoly_pVanish` — **(S2 core)** `substPoly p q (pVanish v) = pVanish (mergeVec p q v)`: the
  substitution merges the `(n−1)` and `j*` factors at the polynomial level.
* `substPoly_relation_transport` — **(S2)** a vanishing relation `∑ₗ pVanish (V l) · A l = 0`
  transports to `∑ₗ pVanish (mergeVec p q (V l)) · substPoly (A l) = 0`.
* `substPoly_natDegree_le` — **(S3 budget)** the substitution does not raise degree, so a valid
  coefficient stays valid.
* `C_subX_dvd_of_substPoly_eq_zero` — **(S4)** if `substPoly p q A = 0` then
  `C (X p − X q) ∣ A` in `R[X]` (coefficient-wise via `C_dvd_iff_dvd_coeff`).
* `C_subX_ne_zero`, `cancel_common_factor` — **(S5 cancellation half)** the common factor
  `C (X p − X q)` is nonzero and cancels from a relation in the domain `R[X]`.

## Residual (the recognized-hard kernel, NOT proven here)

Assembling these into `LovettMergeIndep` still needs: (a) the dimension reindexing
`Fin n → Fin (n−1)` that lets `substPoly`-transported relations be read as `pFamUnion` combinations
over the merged dimension and invoke the `n`-IH (`shape (iii)` bookkeeping — `j* < n−1`); and
(b) the minimal-counterexample / measure-drop contradiction that closes the substitute-back step
(`cancel_common_factor` is only its domain half).  Those two are the remaining open content.

Issue #389.
-/

open Polynomial Finset MvPolynomial

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n : ℕ}

/-- The merge substitution `X_p ↦ X_q` lifted coefficient-wise to `R[X]`
(`R = MvPolynomial (Fin n) F`), as a ring hom. -/
noncomputable def substPoly (p q : Fin n) :
    (MvPolynomial (Fin n) F)[X] →+* (MvPolynomial (Fin n) F)[X] :=
  Polynomial.mapRingHom (substVar (F := F) p q).toRingHom

@[simp] theorem substPoly_X (p q : Fin n) :
    substPoly (F := F) p q Polynomial.X = Polynomial.X := by
  simp [substPoly]

@[simp] theorem substPoly_C (p q : Fin n) (a : MvPolynomial (Fin n) F) :
    substPoly (F := F) p q (Polynomial.C a) = Polynomial.C (substVar (F := F) p q a) := by
  simp [substPoly]

theorem substPoly_xSubC (p q : Fin n) (a : MvPolynomial (Fin n) F) :
    substPoly (F := F) p q (Polynomial.X - Polynomial.C a)
      = Polynomial.X - Polynomial.C (substVar (F := F) p q a) := by
  rw [map_sub, substPoly_X, substPoly_C]

/-- `substPoly` sends `xSubA i` to `xSubA i` if `i ≠ p`, else to `xSubA q` (the merge target). -/
theorem substPoly_xSubA (p q i : Fin n) :
    substPoly (F := F) p q (xSubA i) = xSubA (if i = p then q else i) := by
  rw [xSubA, substPoly_xSubC, xSubA]
  congr 1
  congr 1
  by_cases h : i = p
  · subst h; rw [substVar_X_self, if_pos rfl]
  · rw [substVar_X_of_ne h, if_neg h]

/-- The merged vector in dimension `n`: move the `p`-mass onto `q`, zero out `p`. -/
def mergeVec (p q : Fin n) (v : Fin n → ℕ) : Fin n → ℕ :=
  Function.update (Function.update v p 0) q (v q + v p)

/-- **(S1 core) Weight preservation.**  Merging coordinate `p` onto `q` (`p ≠ q`) preserves the
total weight `|v|`. -/
theorem vAbs_mergeVec (p q : Fin n) (hpq : p ≠ q) (v : Fin n → ℕ) :
    vAbs (mergeVec p q v) = vAbs v := by
  classical
  rw [vAbs, vAbs, mergeVec]
  have hp_mem : p ∈ (Finset.univ \ {q} : Finset (Fin n)) := by
    simp [Finset.mem_sdiff, hpq]
  -- LHS: update at q, then isolate p in the remainder.
  rw [Finset.sum_update_of_mem (Finset.mem_univ q),
      Finset.sum_update_of_mem hp_mem]
  -- RHS: ∑ v = v q + (v p + ∑_{(univ\{q})\{p}} v)
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ q) v,
      Finset.sum_eq_add_sum_diff_singleton_of_mem hp_mem v]
  omega

/-- **(S2 core) `pVanish` transport.**  `substPoly p q (pVanish v) = pVanish (mergeVec p q v)`:
the substitution `X_p ↦ X_q` merges the `p`-factor onto the `q`-factor at the level of the
vanishing polynomial. -/
theorem substPoly_pVanish (p q : Fin n) (hpq : p ≠ q) (v : Fin n → ℕ) :
    substPoly (F := F) p q (pVanish v) = pVanish (mergeVec p q v) := by
  classical
  rw [pVanish, map_prod]
  -- LHS = ∏ i (xSubA (if i = p then q else i))^(v i)
  have hLHS : ∀ i, substPoly (F := F) p q ((xSubA i) ^ (v i))
      = (xSubA (if i = p then q else i)) ^ (v i) := by
    intro i; rw [map_pow, substPoly_xSubA]
  simp_rw [hLHS]
  rw [pVanish]
  -- Both sides: pull out p and q, equate the rest.
  have hmem_p : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  set f : Fin n → (MvPolynomial (Fin n) F)[X] :=
    fun i => (xSubA (if i = p then q else i)) ^ (v i) with hf
  set g : Fin n → (MvPolynomial (Fin n) F)[X] :=
    fun i => (xSubA i) ^ (mergeVec p q v i) with hg
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem_p f,
      Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem_p g]
  have hmem_q' : q ∈ (Finset.univ \ {p} : Finset (Fin n)) := by
    simp [Finset.mem_sdiff, hpq.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem_q' f,
      Finset.prod_eq_mul_prod_diff_singleton_of_mem hmem_q' g]
  -- f p = (xSubA q)^(v p); g p = (xSubA p)^0 = 1
  have hfp : f p = (xSubA (F := F) q) ^ (v p) := by rw [hf]; simp
  have hgp : g p = 1 := by
    rw [hg]; simp only [mergeVec, Function.update_of_ne hpq, Function.update_self, pow_zero]
  -- f q = (xSubA q)^(v q); g q = (xSubA q)^(v q + v p)
  have hfq : f q = (xSubA (F := F) q) ^ (v q) := by rw [hf]; simp [hpq.symm]
  have hgq : g q = (xSubA (F := F) q) ^ (v q + v p) := by
    rw [hg]; simp only [mergeVec, Function.update_self]
  rw [hfp, hgp, hfq, hgq]
  -- the leftover products (over univ \ {p} \ {q}) agree pointwise
  have hrest : ∀ i ∈ ((Finset.univ \ {p}) \ {q} : Finset (Fin n)), f i = g i := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_singleton] at hi
    obtain ⟨⟨_, hip⟩, hiq⟩ := hi
    rw [hf, hg]
    simp only [if_neg hip]
    congr 2
    simp only [mergeVec]
    rw [Function.update_of_ne hiq, Function.update_of_ne hip]
  rw [Finset.prod_congr rfl hrest]
  ring

/-- **(S4) Coefficient-wise divisibility.**  If the lifted substitution kills `A ∈ R[X]`, then
`C (X p − X q)` divides `A` in `R[X]` (every coefficient of `A` is killed by `substVar p q`, hence
divisible by `X p − X q` in `R`; assembled via `C_dvd_iff_dvd_coeff`). -/
theorem C_subX_dvd_of_substPoly_eq_zero {p q : Fin n} {A : (MvPolynomial (Fin n) F)[X]}
    (h : substPoly (F := F) p q A = 0) :
    (Polynomial.C (MvPolynomial.X p - MvPolynomial.X q)) ∣ A := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have hci : substVar (F := F) p q (A.coeff i) = 0 := by
    have : (substPoly (F := F) p q A).coeff i = substVar (F := F) p q (A.coeff i) := by
      simp [substPoly, Polynomial.coeff_map]
    rw [h] at this; simpa using this.symm
  exact sub_X_dvd_of_subst_eq_zero hci

/-- **(S3 budget) Degree non-increase.**  The lifted substitution does not increase degree, so a
coefficient `A` valid below the budget `k − |V l|` stays valid (`substPoly` is `Polynomial.map`). -/
theorem substPoly_natDegree_le (p q : Fin n) (A : (MvPolynomial (Fin n) F)[X]) :
    (substPoly (F := F) p q A).natDegree ≤ A.natDegree := by
  simpa [substPoly] using
    Polynomial.natDegree_map_le (f := (substVar (F := F) p q).toRingHom) (p := A)

/-- **(S2) Relation transport.**  Applying the lifted substitution to a vanishing relation
`∑ₗ pVanish (V l) · A l = 0` yields `∑ₗ pVanish (mergeVec p q (V l)) · substPoly (A l) = 0`,
because `substPoly` is a ring hom (commutes with `∑`, `·`) and `substPoly_pVanish` rewrites each
factor. -/
theorem substPoly_relation_transport {m : ℕ} (p q : Fin n) (hpq : p ≠ q)
    (V : Fin m → (Fin n → ℕ)) (A : Fin m → (MvPolynomial (Fin n) F)[X])
    (hrel : ∑ l, pVanish (F := F) (V l) * A l = 0) :
    ∑ l, pVanish (F := F) (mergeVec p q (V l)) * substPoly (F := F) p q (A l) = 0 := by
  have := congrArg (substPoly (F := F) p q) hrel
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_mul, substPoly_pVanish p q hpq]

/-- `C (X p − X q)` is nonzero in `R[X]` when `p ≠ q` (since `X p ≠ X q` in `R`). -/
theorem C_subX_ne_zero {p q : Fin n} (hpq : p ≠ q) :
    (Polynomial.C (MvPolynomial.X p - MvPolynomial.X q) : (MvPolynomial (Fin n) F)[X]) ≠ 0 := by
  rw [Ne, Polynomial.C_eq_zero, sub_eq_zero]
  exact fun h => hpq (MvPolynomial.X_injective h)

/-- **(S5 cancellation half).**  In the integral domain `R[X]`, a common nonzero factor
`C (X p − X q)` cancels from a vanishing relation `∑ₗ pVanish (V l) · (C(Xp−Xq) · B l) = 0`,
producing the relation `∑ₗ pVanish (V l) · B l = 0`.  (This is the domain step of Lovett's
substitute-back; the minimality/measure-drop contradiction that *closes* the argument is the
remaining recognized-hard kernel and is NOT proven here.) -/
theorem cancel_common_factor {m : ℕ} {p q : Fin n} (hpq : p ≠ q)
    (V : Fin m → (Fin n → ℕ)) (B : Fin m → (MvPolynomial (Fin n) F)[X])
    (hrel : ∑ l, pVanish (F := F) (V l) *
      (Polynomial.C (MvPolynomial.X p - MvPolynomial.X q) * B l) = 0) :
    ∑ l, pVanish (F := F) (V l) * B l = 0 := by
  set c : (MvPolynomial (Fin n) F)[X] := Polynomial.C (MvPolynomial.X p - MvPolynomial.X q) with hc
  have hfac : c * ∑ l, pVanish (F := F) (V l) * B l = 0 := by
    rw [Finset.mul_sum, ← hrel]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  exact (mul_eq_zero.mp hfac).resolve_left (C_subX_ne_zero hpq)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.substPoly_xSubA
#print axioms ArkLib.GMMDS.vAbs_mergeVec
#print axioms ArkLib.GMMDS.substPoly_pVanish
#print axioms ArkLib.GMMDS.substPoly_relation_transport
#print axioms ArkLib.GMMDS.substPoly_natDegree_le
#print axioms ArkLib.GMMDS.C_subX_dvd_of_substPoly_eq_zero
#print axioms ArkLib.GMMDS.C_subX_ne_zero
#print axioms ArkLib.GMMDS.cancel_common_factor
