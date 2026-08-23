/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Distinct-irreducible-factor count over a field

For a polynomial `p : K[X]` over a *field* `K`, the number of DISTINCT irreducible factors of `p`
is at most `p.natDegree`.

Unlike the in-tree `F[Z][X]` count
`pg_card_normalizedFactors_toFinset_le_natDegree` (in `BCIKS20.ListDecoding.Extraction`), which
needs `p.Separable` because the coefficient ring `F[Z]` is *not* a field and admits constant-in-`X`
irreducible factors of `X`-degree `0`, the field-base statement needs **no separability
hypothesis**: every irreducible factor of a polynomial over a field is non-constant
(`Irreducible.natDegree_pos`), so the number of distinct factors is bounded by the total degree.

This is the function-field analogue (`K = F(Z)`) of the list-size degree bound used in
Guruswami–Sudan extraction: the distinct irreducible factors of the interpolant over `K` index the
candidate messages, and their number is `≤ deg_Y` of the interpolant. It supplies the shape of the
`hYbound : Index.card ≤ ℓ` field of `Hab25JohnsonAlgebraicData` (issue #68) for any GS factorisation
carried out over a field rather than over `F[Z]`.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]
  [UniqueFactorizationMonoid R[X]] [NormalizationMonoid R[X]] [DecidableEq R[X]]

/-- Over an integral domain, the number of DISTINCT positive-degree normalized factors of a
polynomial `p : R[X]` is at most `p.natDegree`.

This is the separability-free form needed when the coefficient ring is not a field: degree-zero
content factors may occur, so the theorem counts only factors with positive `X`-degree. -/
theorem card_posNatDegree_normalizedFactors_toFinset_le_natDegree
    (p : R[X]) (hp : p ≠ 0) :
    (((normalizedFactors p).toFinset).filter (fun q : R[X] => 0 < q.natDegree)).card
      ≤ p.natDegree := by
  classical
  let s : Multiset R[X] := normalizedFactors p
  let sPos : Multiset R[X] := s.filter (fun q : R[X] => 0 < q.natDegree)
  have hzero : (0 : R[X]) ∉ s := by
    simpa [s] using (zero_notMem_normalizedFactors p)
  have hfin :
      (((normalizedFactors p).toFinset).filter (fun q : R[X] => 0 < q.natDegree)).card
        = sPos.toFinset.card := by
    congr
    simp [s, sPos, Multiset.toFinset_filter]
  have hcard_toFinset : sPos.toFinset.card ≤ sPos.card :=
    Multiset.toFinset_card_le sPos
  have hcard_le_sum : sPos.card ≤ (sPos.map natDegree).sum := by
    have hmem : ∀ x ∈ sPos.map natDegree, 1 ≤ x := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
      exact (Multiset.mem_filter.1 hq).2
    have h := Multiset.card_nsmul_le_sum hmem
    simpa [Multiset.card_map, smul_eq_mul, mul_one] using h
  have hsplit :
      (s.map natDegree).sum
        = (sPos.map natDegree).sum
          + (((s.filter (fun q : R[X] => ¬ 0 < q.natDegree))).map natDegree).sum := by
    conv_lhs => rw [← Multiset.filter_add_not (fun q : R[X] => 0 < q.natDegree) s]
    rw [Multiset.map_add, Multiset.sum_add]
  have hpos_sum_le : (sPos.map natDegree).sum ≤ (s.map natDegree).sum := by
    rw [hsplit]
    exact Nat.le_add_right _ _
  have hsum : (s.map natDegree).sum = p.natDegree := by
    have hprod : s.prod.natDegree = (s.map natDegree).sum :=
      natDegree_multiset_prod (t := s) hzero
    have hassoc : Associated s.prod p := by
      simpa [s] using (prod_normalizedFactors (a := p) hp)
    have hdeg : s.prod.natDegree = p.natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
    rw [← hprod, hdeg]
  rw [hfin]
  exact hcard_toFinset.trans (hcard_le_sum.trans (hpos_sum_le.trans hsum.le))

/-- Degree-budget corollary of
`card_posNatDegree_normalizedFactors_toFinset_le_natDegree`. -/
theorem card_posNatDegree_normalizedFactors_toFinset_le_of_natDegree_le
    (p : R[X]) (hp0 : p ≠ 0) {ell : ℕ} (hp : p.natDegree ≤ ell) :
    (((normalizedFactors p).toFinset).filter (fun q : R[X] => 0 < q.natDegree)).card ≤ ell :=
  (card_posNatDegree_normalizedFactors_toFinset_le_natDegree p hp0).trans hp

variable {K : Type*} [Field K] [NormalizationMonoid K] [DecidableEq K]

/-- Over a field, the number of DISTINCT irreducible factors of a polynomial `p : K[X]` is at most
`p.natDegree`. No separability hypothesis: each irreducible factor has positive degree because
non-units over a field are non-constant. -/
theorem card_normalizedFactors_toFinset_le_natDegree (p : K[X]) :
    (normalizedFactors p).toFinset.card ≤ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine (Multiset.toFinset_card_le _).trans ?_
  have hzero : (0 : K[X]) ∉ normalizedFactors p := zero_notMem_normalizedFactors p
  have hsum : ((normalizedFactors p).map natDegree).sum = p.natDegree := by
    have h1 : (normalizedFactors p).prod.natDegree = ((normalizedFactors p).map natDegree).sum :=
      natDegree_multiset_prod (normalizedFactors p) hzero
    have h2 : (normalizedFactors p).prod.natDegree = p.natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hp))
    rw [← h1, h2]
  have hmem : ∀ x ∈ (normalizedFactors p).map natDegree, 1 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    exact (irreducible_of_normalized_factor q hq).natDegree_pos
  have key := Multiset.card_nsmul_le_sum hmem
  simp only [Multiset.card_map, smul_eq_mul, mul_one, hsum] at key
  exact key

/-- Degree-budget corollary of `card_normalizedFactors_toFinset_le_natDegree`.

If an external construction bounds `p.natDegree` by `ell`, then the number of distinct
normalized irreducible factors is bounded by the same `ell`. This is the direct `hYbound`
shape used by Hab25 algebraic-data packages. -/
theorem card_normalizedFactors_toFinset_le_of_natDegree_le
    (p : K[X]) {ell : ℕ} (hp : p.natDegree ≤ ell) :
    (normalizedFactors p).toFinset.card ≤ ell :=
  (card_normalizedFactors_toFinset_le_natDegree p).trans hp

/-- Strict degree-budget corollary of `card_normalizedFactors_toFinset_le_natDegree`. -/
theorem card_normalizedFactors_toFinset_lt_of_natDegree_lt
    (p : K[X]) {ell : ℕ} (hp : p.natDegree < ell) :
    (normalizedFactors p).toFinset.card < ell :=
  lt_of_le_of_lt (card_normalizedFactors_toFinset_le_natDegree p) hp

end Polynomial

#print axioms Polynomial.card_normalizedFactors_toFinset_le_natDegree
#print axioms Polynomial.card_normalizedFactors_toFinset_le_of_natDegree_le
#print axioms Polynomial.card_normalizedFactors_toFinset_lt_of_natDegree_lt
#print axioms Polynomial.card_posNatDegree_normalizedFactors_toFinset_le_natDegree
#print axioms Polynomial.card_posNatDegree_normalizedFactors_toFinset_le_of_natDegree_le
