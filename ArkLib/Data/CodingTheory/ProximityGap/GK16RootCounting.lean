/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# GK16 root-multiplicity counting (subspace-design degree budget)

The final counting step of Guruswami–Kopparty "Explicit Subspace Designs"
(FOCS'13 / Combinatorica'16), Theorem 13 / Theorem 14, §4.

The folded-Wronskian determinant `L(X)` of a basis of a `d`-dimensional space
`W ⊆ F[X]_{<k}` is a **nonzero** polynomial of degree `≤ (k-1)·s` (the degree
bound is `ArkLib.FRS.GK16.natDegree_foldedWronskian_le`; the nonvanishing is
GK16 Lemma 12). GK16 then shows `mult(L, β) ≥ dim(W ∩ H_β)` at each evaluation
basepoint `β`, and concludes

  `∑_β dim(W ∩ H_β)  ≤  ∑_β mult(L, β)  ≤  deg(L)`

— the design sum is bounded by the degree because **a nonzero polynomial's
root multiplicities, summed over distinct points, never exceed its degree**.

This file proves that combinatorial counting core, which is the engine of the
GK16 conclusion (the line `(m-1)s ≥ ∑_β mult(L,β) ≥ … ∑_α dim(W ∩ H_α)` on
p. 9 of GK16). It is field-and-code agnostic: a pure statement about polynomials.

## Main statements

- `Polynomial.sum_rootMultiplicity_le_card_roots` — for distinct points `S`,
  `∑_{a∈S} rootMultiplicity a p ≤ p.roots.card`.
- `Polynomial.sum_rootMultiplicity_le_natDegree` — for distinct points `S` and
  `p ≠ 0`, `∑_{a∈S} rootMultiplicity a p ≤ p.natDegree`.

Compiles sorry-free; `#print axioms` gives exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## References

- [GK16] Guruswami-Kopparty. *Explicit Subspace Designs*. Combinatorica 36(2),
  2016. §4.1 Theorem 13, §4.2 Theorem 14 (Claim 16 + the degree-budget line).
-/

open Polynomial

namespace Polynomial

variable {F : Type*} [CommRing F] [IsDomain F]

/-- **GK16 degree-budget counting (multiset form).** For any finite set `S` of
*distinct* points, the total root multiplicity of `p` over `S` is at most the
cardinality of the root multiset `p.roots`.

This is the combinatorial heart of GK16 Theorem 13/14: each distinct basepoint
`β` contributes `rootMultiplicity β p = p.roots.count β`, and the counts over
distinct values cannot exceed the multiset size. -/
theorem sum_rootMultiplicity_le_card_roots (p : F[X]) (S : Finset F) :
    (∑ a ∈ S, rootMultiplicity a p) ≤ Multiset.card p.roots := by
  classical
  -- Rewrite each multiplicity as a multiset count, then restrict to the support.
  have hcount : ∀ a ∈ S, rootMultiplicity a p = p.roots.count a := fun a _ =>
    (count_roots p (a := a)).symm
  rw [Finset.sum_congr rfl hcount]
  -- Drop the points of `S` that are not actual roots (their count is `0`).
  rw [← Finset.sum_filter_ne_zero]
  -- Every surviving point lies in `p.roots.toFinset`.
  have hsub : (S.filter fun a => p.roots.count a ≠ 0) ⊆ p.roots.toFinset := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero ha.2))
  calc (∑ a ∈ S.filter fun a => p.roots.count a ≠ 0, p.roots.count a)
      ≤ ∑ a ∈ p.roots.toFinset, p.roots.count a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq p.roots

/-- **GK16 degree budget (degree form).** For a *nonzero* polynomial `p` and any
finite set `S` of distinct points, the total root multiplicity over `S` is at
most `natDegree p`.

This is the exact inequality `∑_β mult(L, β) ≤ deg(L)` used at the end of the
proofs of GK16 Theorems 13 and 14: combined with `mult(L, β) ≥ dim(W ∩ H_β)`
and `deg(L) ≤ (k-1)·s` it yields the subspace-design bound. -/
theorem sum_rootMultiplicity_le_natDegree (p : F[X]) (_hp : p ≠ 0) (S : Finset F) :
    (∑ a ∈ S, rootMultiplicity a p) ≤ p.natDegree :=
  (sum_rootMultiplicity_le_card_roots p S).trans (card_roots' p)

end Polynomial

/- Axiom audit:
`Polynomial.sum_rootMultiplicity_le_card_roots` and
`Polynomial.sum_rootMultiplicity_le_natDegree` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. -/
