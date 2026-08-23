/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# The general-`k` orchard sum-zero law (#389)

`CubicOrchardIdentity.lean` proves, for `k = 2`, that the deepest-band (agreement-3) supply
of `x^3` equals the zero-sum-**triple** count.  This file lands the **mathematical heart of
the general-`k` generalization** (any rate): the Vieta argument that forces the agreement
points to sum to zero.

> **`sum_eq_zero_of_agree`** — if a degree-`<k` polynomial `P` agrees with `x^{k+1}` on a set
> `T` of `k+1` distinct field elements, then `∑_{a∈T} a = 0`.

Mechanism: `Q := X^{k+1} − P` is **monic of degree `k+1`** (since `deg P < k`), with **`x^k`-
coefficient `0`** (neither `X^{k+1}` nor the degree-`<k` `P` contributes to `x^k`).  `Q`
vanishes on the `k+1` distinct points of `T`, so `Q.roots = T` (multiset, by cardinality),
`Q` splits, and `Splits.nextCoeff_eq_neg_sum_roots_of_monic` reads its `x^k`-coefficient as
`−∑ roots = −∑_{a∈T} a`.  Hence `∑_{a∈T} a = 0`.

This is the agreement → zero-sum direction of the general orchard identity, extending the
`k = 2` cubic case to **every rate**: the deepest pre-capacity (sub-Johnson) supply of the
tower-shaped word `x^{k+1}` is controlled by `(k+1)`-subsets of the domain summing to zero,
whose char-0 vanishing is governed by the prime structure of `k+1` (Mann–Conway–Jones; the
`k = 2` case is the `3 ∣ n` dichotomy in `CubeDichotomyCharZero.lean`).  Issue #389.
-/

open Polynomial
namespace ProximityGap.GeneralOrchard

variable {F : Type*} [Field F]

/-- **The general orchard sum-zero law (forward).**  If a degree-`<k` polynomial `P` agrees
with `x^{k+1}` on a set `T` of `k+1` distinct field elements, then `∑_{a∈T} a = 0` — the
`x^k`-coefficient of the monic degree-`(k+1)` polynomial `X^{k+1} − P` (which vanishes on
`T`, so equals `∏_{a∈T}(X − a)`) is `0`, and Vieta reads it as `−∑ a`. -/
theorem sum_eq_zero_of_agree (P : F[X]) {k : ℕ} (hk : 1 ≤ k) (hPdeg : P.degree < k)
    (T : Finset F) (hTcard : T.card = k + 1)
    (hT : ∀ a ∈ T, P.eval a = a ^ (k + 1)) :
    ∑ a ∈ T, a = 0 := by
  classical
  set Q : F[X] := X ^ (k + 1) - P with hQ
  -- Q is monic of degree k+1
  have hPdeg' : P.degree < (k + 1 : ℕ) := lt_trans hPdeg (by exact_mod_cast Nat.lt_succ_self k)
  have hQmonic : Q.Monic := monic_X_pow_sub hPdeg'
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hQdeg : Q.degree = (k + 1 : ℕ) := by
    rw [hQ, degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  have hQnatDeg : Q.natDegree = k + 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq hQne).mp hQdeg
  -- every a ∈ T is a root of Q
  have hroot : ∀ a ∈ T, Q.eval a = 0 := by
    intro a ha
    rw [hQ, eval_sub, eval_pow, eval_X, hT a ha, sub_self]
  -- T.val ≤ Q.roots, and cards agree, so equal
  have hTle : T.val ≤ Q.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ T
    · have h1 : T.val.count a = 1 := Multiset.count_eq_one_of_mem T.nodup ha
      have h2 : 1 ≤ Q.roots.count a := by
        rw [count_roots]
        exact (rootMultiplicity_pos hQne).mpr (hroot a ha)
      omega
    · have h0 : T.val.count a = 0 := Multiset.count_eq_zero_of_notMem ha
      omega
  have hcardroots : Multiset.card Q.roots ≤ Q.natDegree := Q.card_roots'
  have hTval : Multiset.card T.val = k + 1 := hTcard
  have heq : Q.roots = T.val := by
    refine (Multiset.eq_of_le_of_card_le hTle ?_).symm
    rw [hTval, ← hQnatDeg]; exact hcardroots
  -- splits, nextCoeff = -sum roots
  have hsplits : Splits Q := by
    rw [splits_iff_card_roots, heq, hTval, hQnatDeg]
  have hnext : Q.nextCoeff = - Q.roots.sum :=
    hsplits.nextCoeff_eq_neg_sum_roots_of_monic hQmonic
  -- nextCoeff Q = coeff k Q = 0
  have hnext0 : Q.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega : 0 < Q.natDegree), hQnatDeg]
    simp only [Nat.add_sub_cancel, hQ, coeff_sub, coeff_X_pow]
    have hPk : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_degree_lt hPdeg
    simp [hPk]
  have hrs : Q.roots.sum = 0 := by
    have hz : (0 : F) = - Q.roots.sum := hnext0 ▸ hnext
    linear_combination hz
  rw [heq] at hrs
  rw [Finset.sum_eq_multiset_sum, Multiset.map_id']
  exact hrs

/-- **The general orchard construction (backward).**  Every `k+1`-subset `T` of the field
summing to zero is realized by a degree-`<k` polynomial agreeing with `x^{k+1}` on `T`:
take `P := X^{k+1} − ∏_{a∈T}(X − a)`, whose top two coefficients vanish (`x^{k+1}` cancels,
`x^k` is `nextCoeff ∏ = −∑ a = 0`). -/
theorem exists_agree_of_sum_zero {k : ℕ} (T : Finset F) (hTcard : T.card = k + 1)
    (hsum : ∑ a ∈ T, a = 0) :
    ∃ P : F[X], P.degree < (k : ℕ) ∧ ∀ a ∈ T, P.eval a = a ^ (k + 1) := by
  classical
  set Q : F[X] := ∏ a ∈ T, (X - C a) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hQnat : Q.natDegree = k + 1 := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [natDegree_X_sub_C, hTcard]
  have hQnext : Q.nextCoeff = 0 := by
    rw [hQ, Monic.nextCoeff_prod _ _ (fun a _ => monic_X_sub_C a)]
    simp only [nextCoeff_X_sub_C]
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hQcoeffk : Q.coeff k = 0 := by
    have hnc := nextCoeff_of_natDegree_pos (p := Q) (by omega : 0 < Q.natDegree)
    rw [hQnat, show k + 1 - 1 = k from rfl] at hnc
    rw [← hnc, hQnext]
  have hQlead : Q.coeff (k + 1) = 1 := by
    have := hQmonic.coeff_natDegree; rwa [hQnat] at this
  refine ⟨X ^ (k + 1) - Q, ?_, ?_⟩
  · -- degree < k: coeff j = 0 for all j ≥ k
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    have hjk : k ≤ j := by exact_mod_cast hj
    rw [coeff_sub, coeff_X_pow]
    by_cases hjk1 : j = k + 1
    · rw [if_pos hjk1, hjk1, hQlead]; ring
    · rw [if_neg hjk1]
      have hQj : Q.coeff j = 0 := by
        rcases eq_or_lt_of_le hjk with hje | hjl
        · rw [← hje, hQcoeffk]
        · exact coeff_eq_zero_of_natDegree_lt (by rw [hQnat]; omega)
      rw [hQj]; ring
  · intro a ha
    have hQa : Q.eval a = 0 := by
      rw [hQ, eval_prod]
      exact Finset.prod_eq_zero ha (by simp)
    simp only [eval_sub, eval_pow, eval_X, hQa, sub_zero]

/-- **The general orchard "iff".**  For a `k+1`-subset `T` (distinct field elements): some
degree-`<k` polynomial agrees with `x^{k+1}` on all of `T` **iff** `∑_{a∈T} a = 0`. -/
theorem agree_iff_sum_zero {k : ℕ} (hk : 1 ≤ k) (T : Finset F) (hTcard : T.card = k + 1) :
    (∃ P : F[X], P.degree < (k : ℕ) ∧ ∀ a ∈ T, P.eval a = a ^ (k + 1))
      ↔ ∑ a ∈ T, a = 0 := by
  constructor
  · rintro ⟨P, hPdeg, hP⟩
    exact sum_eq_zero_of_agree P hk hPdeg T hTcard hP
  · exact exists_agree_of_sum_zero T hTcard

end ProximityGap.GeneralOrchard

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.GeneralOrchard.sum_eq_zero_of_agree
#print axioms ProximityGap.GeneralOrchard.exists_agree_of_sum_zero
#print axioms ProximityGap.GeneralOrchard.agree_iff_sum_zero
