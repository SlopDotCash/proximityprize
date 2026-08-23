/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTExponentGridSum
import ArkLib.Data.CodingTheory.ProximityGap.CRTPacketMinpoly

/-!
# Issue #232 — the de Bruijn splice: the two-prime subset-sum fiber slice, no hypothesis

The O79 step-(1) entry (DISPROOF_LOG) closed the packet minimal polynomial over the
coprime cyclotomic extension (`CRTPacketMinpoly`) and named the next move: *"a parallel
lane's `CRTExponentGridSum.lean` (step (2), `fiber_slice_of_vanishing_subset_sum`)
carries exactly this minpoly statement as its open `hmin` hypothesis — composing the two
yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not
built this pass to avoid depending on an unlanded sibling file."*  Both siblings are now
on `main`; this file is that splice.

* `vanishing_subset_sum_fiber_slice` — **the unconditional statement**: for distinct
  primes `p ≠ q`, `0 < b`, a primitive `(p^a · q^b)`-th root of unity `ζ` in ANY
  characteristic-zero field, and ANY subset `S ⊆ ZMod (p^a · q^b)` with
  `∑_{e ∈ S} ζ^e = 0`, the fiber sums of the CRT grid set of `S` are invariant under
  μ_q-shifts of the `η`-coordinate:

      ∑_{j < p^a} [(j, i·q^{b-1} + s) ∈ gridSet S] · (ζ^{q^b})^j

  is independent of `i < q` (for each residue `s < q^{b-1}`).  No minimal-polynomial,
  intermediate-field, or cyclotomic hypothesis remains — only the primitive root and the
  vanishing subset sum.  Proof: `CRTExponentGridSum.subset_sum_eq_grid_double_sum`
  (step (2)) converts the subset sum to the coprime-grid double sum, and
  `CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers` (step (1) + step (0) engine)
  slices it; the two factor primitive roots come from `IsPrimitiveRoot.pow`.

Falsified first (`scripts/probes/probe_debruijn_squarefree.py`, CLAIM A, exit 0):
fiber-sum invariance of vanishing subset sums checked EXACTLY (fiber sums reduced in
`ℤ[x]/Φ_{p^a}(x)`, vanishing tested by exact division by `Φ_n`) — exhaustive over all
`2^n` subsets at `n = 12, 18, 15, 20` (0 violations on 1 156 + 1 000 + 38 + 100
vanishing sets) and sampled+planted at `n = 36` (881 vanishing, 0 violations); the
invariance has teeth (e.g. 1 047 420 of the 2^20 non-vanishing subsets at `n = 20`
violate it).

With this splice the only de Bruijn capstone input left open is step (3) — the
positivity/disjointness extraction (see `DeBruijnSquarefree.lean` for its squarefree
closure).

## References

- [deBruijn53] N. G. de Bruijn, *On the factorization of cyclic groups*, Indag. Math. 15
  (1953).  Tracking issue #232; DISPROOF_LOG O66/O67/O73/O79.
- In-tree: `CRTDoubleSlice` (step 0), `CRTPacketMinpoly` (step 1),
  `CRTExponentGridSum` (step 2).
-/

namespace CRTSubsetSumFiberSlice

open Polynomial Finset CRTExponentGridSum

/-- **The de Bruijn two-prime subset-sum fiber slice, unconditionally** (steps
(0)+(1)+(2) composed): a vanishing subset sum of `μ_{p^a·q^b}` exponents in any
characteristic-zero field has μ_q-shift invariant fiber sums over its CRT grid set.
Only the primitive root and the vanishing sum are assumed. -/
theorem vanishing_subset_sum_fiber_slice
    {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    (S : Finset (ZMod (p ^ a * q ^ b)))
    (hsum : ∑ e ∈ S, ζ ^ e.val = 0)
    {i i' s : ℕ} (hi : i < q) (hi' : i' < q) (hs : s < q ^ (b - 1)) :
    (∑ j ∈ Finset.range (p ^ a),
        if (j, i * q ^ (b - 1) + s) ∈ gridSet (p ^ a) (q ^ b) S
          then (ζ ^ q ^ b) ^ j else 0)
      = ∑ j ∈ Finset.range (p ^ a),
          if (j, i' * q ^ (b - 1) + s) ∈ gridSet (p ^ a) (q ^ b) S
            then (ζ ^ q ^ b) ^ j else 0 := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hqb : 0 < q ^ b := pow_pos hq.pos b
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)
  -- the two factor primitive roots
  have hξ : IsPrimitiveRoot (ζ ^ q ^ b) (p ^ a) :=
    hζ.pow (Nat.mul_pos hpa hqb) (mul_comm (p ^ a) (q ^ b))
  have hη : IsPrimitiveRoot (ζ ^ p ^ a) (q ^ b) :=
    hζ.pow (Nat.mul_pos hpa hqb) rfl
  -- step (2): the grid double sum vanishes
  have hgrid : ∑ x ∈ gridSet (p ^ a) (q ^ b) S,
      (ζ ^ q ^ b) ^ x.1 * (ζ ^ p ^ a) ^ x.2 = 0 := by
    rw [← subset_sum_eq_grid_double_sum hpa hqb hcop hζ.pow_eq_one S]
    exact hsum
  -- steps (0)+(1): slice it
  exact CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers hp hq hpq hb hξ hη
    (gridSet (p ^ a) (q ^ b) S) (gridSet_subset _ _ _) hgrid hi hi' hs

/-- Non-vacuity at a **nonempty vanishing subset sum** in a concrete field: `n = 6 =
2^1·3^1`, `ζ = e^{2πi/6} ∈ ℂ`, `S = {1, 4}` (the rotated `μ_2`-packet `ζ + ζ^4 =
ζ(1 + ζ^3) = 0`).  Every hypothesis is discharged; the fiber-sum invariance across all
three `η`-columns follows from the theorem. -/
example :
    (∑ j ∈ Finset.range (2 ^ 1),
        if (j, 0 * 3 ^ (1 - 1) + 0) ∈
            gridSet (2 ^ 1) (3 ^ 1) ({1, 4} : Finset (ZMod (2 ^ 1 * 3 ^ 1)))
          then ((Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3 ^ 1) ^ j else 0)
      = ∑ j ∈ Finset.range (2 ^ 1),
          if (j, 2 * 3 ^ (1 - 1) + 0) ∈
              gridSet (2 ^ 1) (3 ^ 1) ({1, 4} : Finset (ZMod (2 ^ 1 * 3 ^ 1)))
            then ((Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3 ^ 1) ^ j else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6) with hζdef
  have h6 : IsPrimitiveRoot ζ 6 := by
    have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    norm_num [hζdef] at h ⊢
    exact h
  have hζ : IsPrimitiveRoot ζ (2 ^ 1 * 3 ^ 1) := by norm_num [h6]
  have h3 : ζ ^ 3 = -1 := by
    have h2 : IsPrimitiveRoot (ζ ^ 3) 2 := h6.pow (by norm_num) (by norm_num)
    exact h2.eq_neg_one_of_two_right
  have hsum : ∑ e ∈ ({1, 4} : Finset (ZMod (2 ^ 1 * 3 ^ 1))), ζ ^ e.val = 0 := by
    rw [show ({1, 4} : Finset (ZMod (2 ^ 1 * 3 ^ 1))) = {(1 : ZMod 6), 4} from rfl]
    rw [Finset.sum_pair (by decide)]
    rw [show ((1 : ZMod 6)).val = 1 from rfl, show ((4 : ZMod 6)).val = 4 from rfl]
    have h4 : ζ ^ 4 = ζ ^ 3 * ζ := by ring
    rw [pow_one, h4, h3]
    ring
  exact vanishing_subset_sum_fiber_slice (p := 2) (q := 3) (a := 1) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) one_pos hζ _ hsum
    (by norm_num) (by norm_num) (by norm_num)

end CRTSubsetSumFiberSlice

#print axioms CRTSubsetSumFiberSlice.vanishing_subset_sum_fiber_slice
