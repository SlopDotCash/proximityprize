/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FinCases

/-! # C024: the GM-MDS derandomization counterexample lives in the kernel of the
    KKH26 antipodal sum-invariant (the negation involution acts on BOTH faces).

This file makes the C024 dichotomy a theorem.  The single involution `−1 = ω^{n/2} ∈ μ_n`
is load-bearing in opposite directions:

* COUNT face (`KKH26CharZeroCollisionLaw.sum_eq_iff_freePart_eq`, in-tree, axiom-clean):
  antipodal pairs cancel in subset SUMS, so the antipodal-free part is a complete invariant
  and the char-0 collision count COLLAPSES.
* GENERICITY face (`MuTwoPowDerandRefutation.rimMatrix_det_eq_zero`, in-tree, axiom-clean):
  even polynomials agree on `±x`, so the reduced intersection matrix at the geometric point
  is SINGULAR and the GM-MDS derandomization to capacity FAILS.

The attack-plan claim (`derand_certificate_is_paired`): the GM-MDS counterexample's
*agreement support* — the busy coordinates of `MuTwoPowDerandRefutation.badHypergraph`,
`{0,1,2,4,5,6}`, carrying the points `{±1, ±ω, ±ω²} = {ω^i}` — is a union of antipodal
coordinate-pairs.  As an INDEX set in `Fin 8`, negation is the shift `i ↦ i + 4`, and the
busy set is exactly closed under it: its antipodal-free part is empty.  Hence the bad
certificate sits in the kernel of the KKH26 sum-invariant: both faces have the SAME cause,
paired support.

This is a finite combinatorial fact (decidable); we state it index-side (`Fin 8`) so it is
field-independent and matches the `freePart` mechanism without needing a concrete `ω`.
-/

namespace ProximityGap.C024

open Finset

/-- The busy coordinates of `MuTwoPowDerandRefutation.badHypergraph` (the coordinates where
the agreement hyperedge is nonempty): `{0,1,2,4,5,6}`.  Coordinate `i` carries the geometric
point `ω^i`; the two unused coordinates `3, 7` carry no agreement constraint. -/
def busy : Finset (Fin 8) := {0, 1, 2, 4, 5, 6}

/-- Negation on the geometric coordinates of `μ_8`: `−(ω^i) = ω^{i+4}` since `ω⁴ = −1`,
so on the INDEX `i : Fin 8` negation is the half-period shift `i ↦ i + 4`. -/
def negIdx (i : Fin 8) : Fin 8 := i + 4

/-- The antipodal-free part of a coordinate set (index side): the indices whose
half-period partner is absent — the exact analogue of
`KKH26CharZeroCollisionLaw.freePart` transported to the index `ω^i ↦ i`. -/
def freePartIdx (S : Finset (Fin 8)) : Finset (Fin 8) :=
  S.filter (fun i => negIdx i ∉ S)

/-- **C024, attack-plan theorem (`derand_certificate_is_paired`).**  The agreement support
of the GM-MDS derandomization counterexample is negation-closed: its antipodal-free part is
empty.  Equivalently, the busy coordinates split into the three antipodal pairs
`{0,4}, {1,5}, {2,6}` (= `±1, ±ω, ±ω²`).  Therefore the bad certificate lies in the kernel
of the KKH26 sum-invariant `freePart` — the genericity obstruction and the count collapse
have a common cause. -/
theorem derand_certificate_is_paired : freePartIdx busy = ∅ := by
  decide

/-- The same fact stated positively: every busy coordinate's half-period partner is also
busy (the support is a union of antipodal pairs). -/
theorem busy_negClosed : ∀ i ∈ busy, negIdx i ∈ busy := by
  decide

/-- The unused coordinates `{3, 7}` are likewise an antipodal pair: the involution
`i ↦ i + 4` preserves the busy/unused split, so the WHOLE coordinate frame is partitioned
into antipodal pairs — there is no coordinate on which the certificate could break the
negation symmetry. -/
theorem unused_negClosed : negIdx 3 = 7 ∧ negIdx 7 = 3 := by
  decide

/-- Sanity: `negIdx` is an involution (negation squared = identity), matching `−(−x) = x`. -/
theorem negIdx_involutive : ∀ i : Fin 8, negIdx (negIdx i) = i := by
  decide

#print axioms derand_certificate_is_paired
#print axioms busy_negClosed

end ProximityGap.C024
