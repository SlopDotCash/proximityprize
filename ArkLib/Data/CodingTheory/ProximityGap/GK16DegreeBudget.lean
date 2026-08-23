/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting
import ArkLib.Data.CodingTheory.ProximityGap.GK16Wronskian

/-!
# GK16 subspace-design degree budget (folded-Wronskian chaining)

The degree-budget conclusion of Guruswami–Kopparty "Explicit Subspace Designs"
(Theorem 13 / Theorem 14, §4), assembled from the two verified halves already in
ArkLib:

* the **degree bound** `natDegree (foldedWronskian P ω) ≤ s·(k-1)`
  (`ArkLib.FRS.GK16.natDegree_foldedWronskian_le`, `ProximityPrizeLeaves.lean`), and
* the **root-multiplicity counting core** `∑_{a∈S} rootMultiplicity a L ≤ natDegree L`
  for a nonzero `L` over distinct points `S`
  (`Polynomial.sum_rootMultiplicity_le_natDegree`, `GK16RootCounting.lean`).

Chaining them gives the central inequality of GK16 §4: for a nonzero folded
Wronskian `L` of `s` polynomials of degree `< k`, the multiplicities of `L` at
any set of distinct basepoints sum to at most `s·(k-1)`:

  `∑_{a∈S} rootMultiplicity a L  ≤  natDegree L  ≤  s·(k-1)`.

In GK16's proof of Theorem 14 (Claim 16), each basepoint `β` carries
`rootMultiplicity β L ≥ dim(W ∩ H_β)`, so this is exactly the line

  `(m-1)s  ≥  ∑_β mult(L, β)  ≥  ∑_α dim(W ∩ H_α)`

on p. 9 of GK16 — i.e. the subspace-design sum is bounded by the degree budget.

## Main statement

- `ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le` — the degree-budget
  inequality above.

## Status for `frs_is_subspaceDesign_gk16`

This file closes the **degree-counting spine** of GK16 §4. The two deep ingredients that were
previously gaps are now **fully closed**:

1. **GK16 Lemma 12, hard direction** — `LinearIndependent F P → foldedWronskian P ω ≠ 0`
   is **fully closed** in `GK16Lemma12.lean` as an unconditional theorem
   `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent`. (The easy direction
   is in `GK16Wronskian.lean`).
2. **GK16 Claim 16** — `rootMultiplicity (domain i) L ≥ dim (A ⊓ ker(eval_i))`
   is **fully closed** in `SubspaceDesign.lean` and `GK16Structural.lean`
   (the structural encoder-isomorphism + adapted-basis transport are completely written
   and `sorry`-free).

Therefore, the entire GK16 §4 degree budget for the FRS half is unconditional and closed.
Only the Univariate Multiplicity (UM) half of ABF26 T2.18 remains deferred.

Compiles sorry-free; `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## References

- [GK16] Guruswami-Kopparty. *Explicit Subspace Designs*. Combinatorica 36(2),
  2016. §4.1 Theorem 13, §4.2 Theorem 14, Claims 15–16; Appendix A (Lemma 12).
-/

open Polynomial

namespace ArkLib.FRS.GK16

/-- **GK16 §4 degree-budget inequality (verified spine).** Let `P : Fin s → F[X]`
be `s` polynomials each of degree `< k` (`natDegree (P j) ≤ k - 1`), with folded
Wronskian `L := foldedWronskian P ω`. If `L ≠ 0`, then for any finite set `S` of
*distinct* field points the root multiplicities of `L` over `S` sum to at most
`s·(k-1)`:

  `∑_{a ∈ S} rootMultiplicity a L  ≤  s·(k-1)`.

This is the assembled conclusion of GK16 Theorem 13/14: it chains the folded-
Wronskian degree bound (`natDegree_foldedWronskian_le`) with the multiplicity-
counting core (`Polynomial.sum_rootMultiplicity_le_natDegree`). Combined with
GK16's Claim 16 (`rootMultiplicity (domain i) L ≥ dim (A ⊓ ker(eval_i))`) it
bounds the subspace-design sum `∑_i dim(A_i) ≤ s·(k-1)`. -/
theorem sum_rootMultiplicity_foldedWronskian_le
    {F : Type*} [Field F] {s k : ℕ}
    (P : Fin s → F[X]) (ω : F)
    (hP : ∀ j, (P j).natDegree ≤ k - 1)
    (hL : foldedWronskian P ω ≠ 0) (S : Finset F) :
    (∑ a ∈ S, rootMultiplicity a (foldedWronskian P ω)) ≤ s * (k - 1) :=
  (Polynomial.sum_rootMultiplicity_le_natDegree _ hL S).trans
    (natDegree_foldedWronskian_le P ω hP)

end ArkLib.FRS.GK16

/- Axiom audit:
`ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le` depends only on
`propext`, `Classical.choice`, and `Quot.sound`. -/
