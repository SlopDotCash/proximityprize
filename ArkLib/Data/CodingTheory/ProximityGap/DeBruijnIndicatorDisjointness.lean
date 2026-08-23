/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CRTPacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.CRTExponentGridSum
import Mathlib.Tactic

/-!
# Issue #232 — de Bruijn step (3), first disjointness brick: the squarefree two-prime case

The O73/O79 ledger left exactly one genuinely de Bruijn input open: the
*positivity/disjointness* step — for `0/1` indicator weights, the μ_q-shift invariant
fiber sums (in-tree: `CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers`) force the
subset to decompose into DISJOINT rotated full prime packets (de Bruijn, *On the
factorisation of cyclic groups*, Indag. Math. 1953).  This file proves that step in
full at the squarefree level `n = p·q` (`a = b = 1`), where the invariance says ALL
fibers are equal:

* `coeffs_all_eq_of_vanishing_prime` — at a single prime, a vanishing ℚ-weighted sum of
  `p`-th roots of unity has ALL coefficients equal (the `m = 0` slice of the in-tree
  `CRTDoubleSlice.weighted_vanishing_slice_rat`).
* `equal_indicator_sums_dichotomy` — **the prime indicator dichotomy**: two `0/1`
  subset sums of μ_p agree iff the subsets are EQUAL, or one is full and the other
  empty.  (The indicator difference has values in `{−1,0,1}` and all values equal.)
* `vanishing_indicator_empty_or_full` — the brief's "nonzero fiber is a full packet"
  form: a vanishing `0/1` sum of μ_p has empty or full support — every nonzero fiber
  is exactly one full μ_p-packet.
* `debruijn_squarefree_two_prime` — **the headline**: for distinct primes `p ≠ q` and a
  primitive `(p·q)`-th root `ζ` in any characteristic-zero field, every subset
  `S ⊆ ZMod (p·q)` with `Σ_{e∈S} ζ^e = 0` is closed under `e ↦ e + p` or closed under
  `e ↦ e + q` — i.e. `S` is a disjoint union of rotated full μ_q-packets, or a
  disjoint union of rotated full μ_p-packets.  PURE type: at the squarefree level no
  mixtures exist (every μ_p-coset and μ_q-coset of `Z_{pq}` intersect), which is
  strictly sharper than de Bruijn's ℕ-combination statement restricted to indicators.

Falsified first (`scripts/probes/probe_indicator_packet_disjointness.py`, exact
arithmetic in `ℤ[x]/Φ_n`, exit 0): the headline and its mechanism EXHAUSTIVELY at
`n = 6, 10, 15` (all `2^n` subsets; both pure types occur; the vanishing hypothesis is
load-bearing — 54 non-vanishing violators at `n = 6`); the verbatim prime-power
extension is REFUTED (24/100 vanishing subsets at `n = 12` and 432/1000 at `n = 18`
violate both closures — mixtures), so `a = b = 1` is the honest scope of this
statement; the open continuation is the packet-combination form (probe check C6:
column indicator differences are divisible by `Φ_{p^a}` — verified 100% at 12 and 18 —
the recursion seed for `a ≥ 2`, where the naive dichotomy fails 168/486 times).

What remains for full de Bruijn (named, not claimed): the prime-power case `a·b > 1`
— replace the dichotomy by "indicator column differences are ℤ-combinations of rotated
`Φ_{p^a}`-packets" and recurse; assembly of mixed disjoint packets at composite levels.
-/

namespace DeBruijnIndicatorDisjointness

open Polynomial Finset

/-- **All coefficients equal at a prime**: a vanishing ℚ-weighted sum of `p`-th roots
of unity (char 0) has all `p` coefficients equal — the `m = 0` slice of
`CRTDoubleSlice.weighted_vanishing_slice_rat`. -/
theorem coeffs_all_eq_of_vanishing_prime {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {a : ℕ → ℚ} (hsum : ∑ e ∈ Finset.range p, a e • ζ ^ e = 0)
    {i i' : ℕ} (hi : i < p) (hi' : i' < p) : a i = a i' := by
  have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  have hsum' : ∑ e ∈ Finset.range (p ^ (0 + 1)), a e • ζ ^ e = 0 := by simpa using hsum
  have h := CRTDoubleSlice.weighted_vanishing_slice_rat hp hζ' hsum'
    (i := i) (i' := i') (s := 0) hi hi' (by norm_num)
  simpa using h

/-- **The prime indicator dichotomy** (the de Bruijn step-(3) engine at a prime): two
`0/1` indicator sums of `p`-th roots of unity agree iff the index sets are equal, or
one is all of `[0,p)` and the other empty.  Mechanism: the indicator difference takes
values in `{−1, 0, 1}` and, by `coeffs_all_eq_of_vanishing_prime`, all its values are
equal. -/
theorem equal_indicator_sums_dichotomy {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {X Y : Finset ℕ} (hX : X ⊆ Finset.range p) (hY : Y ⊆ Finset.range p)
    (h : ∑ j ∈ X, ζ ^ j = ∑ j ∈ Y, ζ ^ j) :
    X = Y ∨ (X = Finset.range p ∧ Y = ∅) ∨ (X = ∅ ∧ Y = Finset.range p) := by
  classical
  have hsum : ∑ e ∈ Finset.range p,
      (((if e ∈ X then (1 : ℚ) else 0) - (if e ∈ Y then (1 : ℚ) else 0)) • ζ ^ e) = 0 := by
    have hX' : ∑ e ∈ Finset.range p, (if e ∈ X then ζ ^ e else 0) = ∑ j ∈ X, ζ ^ j := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hX]
    have hY' : ∑ e ∈ Finset.range p, (if e ∈ Y then ζ ^ e else 0) = ∑ j ∈ Y, ζ ^ j := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hY]
    calc ∑ e ∈ Finset.range p,
        (((if e ∈ X then (1 : ℚ) else 0) - (if e ∈ Y then (1 : ℚ) else 0)) • ζ ^ e)
        = ∑ e ∈ Finset.range p,
            ((if e ∈ X then ζ ^ e else 0) - (if e ∈ Y then ζ ^ e else 0)) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [sub_smul, ite_smul, ite_smul, one_smul, zero_smul]
      _ = (∑ e ∈ Finset.range p, (if e ∈ X then ζ ^ e else 0))
            - ∑ e ∈ Finset.range p, (if e ∈ Y then ζ ^ e else 0) :=
          Finset.sum_sub_distrib ..
      _ = 0 := by rw [hX', hY', h, sub_self]
  have key : ∀ e, e < p →
      ((if e ∈ X then (1 : ℚ) else 0) - (if e ∈ Y then (1 : ℚ) else 0))
        = ((if 0 ∈ X then (1 : ℚ) else 0) - (if 0 ∈ Y then (1 : ℚ) else 0)) :=
    fun e he => coeffs_all_eq_of_vanishing_prime hp hζ hsum he hp.pos
  by_cases h0X : 0 ∈ X <;> by_cases h0Y : 0 ∈ Y
  · -- value 0: X = Y
    left
    ext e
    constructor
    · intro heX
      have h := key e (Finset.mem_range.mp (hX heX))
      rw [if_pos heX, if_pos h0X, if_pos h0Y] at h
      by_contra heY
      rw [if_neg heY] at h
      norm_num at h
    · intro heY
      have h := key e (Finset.mem_range.mp (hY heY))
      rw [if_pos heY, if_pos h0X, if_pos h0Y] at h
      by_contra heX
      rw [if_neg heX] at h
      norm_num at h
  · -- value 1: X full, Y empty
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · refine Finset.Subset.antisymm hX fun e he => ?_
      have h := key e (Finset.mem_range.mp he)
      rw [if_pos h0X, if_neg h0Y] at h
      by_contra heX
      rw [if_neg heX] at h
      by_cases heY : e ∈ Y
      · rw [if_pos heY] at h; norm_num at h
      · rw [if_neg heY] at h; norm_num at h
    · refine Finset.eq_empty_iff_forall_notMem.mpr fun e heY => ?_
      have h := key e (Finset.mem_range.mp (hY heY))
      rw [if_pos heY, if_pos h0X, if_neg h0Y] at h
      by_cases heX : e ∈ X
      · rw [if_pos heX] at h; norm_num at h
      · rw [if_neg heX] at h; norm_num at h
  · -- value −1: X empty, Y full
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · refine Finset.eq_empty_iff_forall_notMem.mpr fun e heX => ?_
      have h := key e (Finset.mem_range.mp (hX heX))
      rw [if_pos heX, if_neg h0X, if_pos h0Y] at h
      by_cases heY : e ∈ Y
      · rw [if_pos heY] at h; norm_num at h
      · rw [if_neg heY] at h; norm_num at h
    · refine Finset.Subset.antisymm hY fun e he => ?_
      have h := key e (Finset.mem_range.mp he)
      rw [if_neg h0X, if_pos h0Y] at h
      by_contra heY
      rw [if_neg heY] at h
      by_cases heX : e ∈ X
      · rw [if_pos heX] at h; norm_num at h
      · rw [if_neg heX] at h; norm_num at h
  · -- value 0: X = Y
    left
    ext e
    constructor
    · intro heX
      have h := key e (Finset.mem_range.mp (hX heX))
      rw [if_pos heX, if_neg h0X, if_neg h0Y] at h
      by_contra heY
      rw [if_neg heY] at h
      norm_num at h
    · intro heY
      have h := key e (Finset.mem_range.mp (hY heY))
      rw [if_pos heY, if_neg h0X, if_neg h0Y] at h
      by_contra heX
      rw [if_neg heX] at h
      norm_num at h

/-- **Every nonzero indicator fiber at a prime is one full μ_p-packet** (the brief's
named candidate, base form): a vanishing `0/1` sum of `p`-th roots of unity has empty
or full support. -/
theorem vanishing_indicator_empty_or_full {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {X : Finset ℕ} (hX : X ⊆ Finset.range p)
    (h : ∑ j ∈ X, ζ ^ j = 0) : X = ∅ ∨ X = Finset.range p := by
  have h' : ∑ j ∈ X, ζ ^ j = ∑ j ∈ (∅ : Finset ℕ), ζ ^ j := by simpa using h
  rcases equal_indicator_sums_dichotomy hp hζ hX (Finset.empty_subset _) h' with
    h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2.1
  · exact Or.inl h3.1

/-! ## Grid fiber sets and the coset-shift bookkeeping -/

/-- The `c`-th fiber (column) set of a grid index set: `{j < N : (j, c) ∈ I}`. -/
def fiberSet (N : ℕ) (I : Finset (ℕ × ℕ)) (c : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (j, c) ∈ I)

lemma mem_fiberSet {N : ℕ} {I : Finset (ℕ × ℕ)} {c j : ℕ} :
    j ∈ fiberSet N I c ↔ j < N ∧ (j, c) ∈ I := by
  simp [fiberSet]

lemma fiberSet_subset (N : ℕ) (I : Finset (ℕ × ℕ)) (c : ℕ) :
    fiberSet N I c ⊆ Finset.range N :=
  Finset.filter_subset _ _

lemma sum_fiberSet {L : Type*} [Semiring L] (ξ : L) (N : ℕ) (I : Finset (ℕ × ℕ))
    (c : ℕ) :
    ∑ j ∈ fiberSet N I c, ξ ^ j
      = ∑ j ∈ Finset.range N, if (j, c) ∈ I then ξ ^ j else 0 := by
  rw [fiberSet, Finset.sum_filter]

/-- **Global form of the prime indicator dichotomy.**  If every pair of columns is
related by the squarefree indicator dichotomy, then either all columns are literally
equal, or every column is empty/full.  This isolates the finite combinatorial split
used by the squarefree de Bruijn theorem. -/
lemma equal_fibers_or_empty_full_of_pairwise_dichotomy {p q : ℕ}
    {I : Finset (ℕ × ℕ)}
    (hdich : ∀ c < q, ∀ c' < q,
      fiberSet p I c = fiberSet p I c'
        ∨ (fiberSet p I c = Finset.range p ∧ fiberSet p I c' = ∅)
        ∨ (fiberSet p I c = ∅ ∧ fiberSet p I c' = Finset.range p)) :
    (∀ c < q, ∀ c' < q, fiberSet p I c = fiberSet p I c')
      ∨ (∀ c < q, fiberSet p I c = ∅ ∨ fiberSet p I c = Finset.range p) := by
  classical
  by_cases hall : ∀ c < q, ∀ c' < q, fiberSet p I c = fiberSet p I c'
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨c₀, hc₀, c₁, hc₁, hne⟩ := hall
    have hempty : ∃ c₂, c₂ < q ∧ fiberSet p I c₂ = ∅ := by
      rcases hdich c₀ hc₀ c₁ hc₁ with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd h hne
      · exact ⟨c₁, hc₁, h⟩
      · exact ⟨c₀, hc₀, h⟩
    obtain ⟨c₂, hc₂, hc₂e⟩ := hempty
    intro c hc
    rcases hdich c hc c₂ hc₂ with h | h | h
    · left
      exact h.trans hc₂e
    · right
      exact h.1
    · left
      exact h.1

/-- Shifting the second CRT coordinate cyclically adds `p` to the encoded exponent:
`g(j, (c+1) % q) = g(j, c) + p` in `ZMod (p·q)`. -/
lemma gridMap_snd_succ {p q : ℕ} (j c : ℕ) :
    CRTExponentGridSum.gridMap p q (j, (c + 1) % q)
      = CRTExponentGridSum.gridMap p q (j, c) + ((p : ℕ) : ZMod (p * q)) := by
  have hsplit : (c + 1) % q * p + (c + 1) / q * (p * q) = (c + 1) * p := by
    calc (c + 1) % q * p + (c + 1) / q * (p * q)
        = ((c + 1) % q + q * ((c + 1) / q)) * p := by ring
      _ = (c + 1) * p := by rw [Nat.mod_add_div]
  have hz : (((c + 1) / q * (p * q) : ℕ) : ZMod (p * q)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have hmain : (((c + 1) % q * p : ℕ) : ZMod (p * q))
      = (((c + 1) * p : ℕ) : ZMod (p * q)) := by
    rw [← hsplit, Nat.cast_add, hz, add_zero]
  show ((j * q + (c + 1) % q * p : ℕ) : ZMod (p * q))
      = ((j * q + c * p : ℕ) : ZMod (p * q)) + ((p : ℕ) : ZMod (p * q))
  rw [Nat.cast_add, Nat.cast_add, hmain]
  push_cast
  ring

/-- Shifting the first CRT coordinate cyclically adds `q` to the encoded exponent:
`g((j+1) % p, c) = g(j, c) + q` in `ZMod (p·q)`. -/
lemma gridMap_fst_succ {p q : ℕ} (j c : ℕ) :
    CRTExponentGridSum.gridMap p q ((j + 1) % p, c)
      = CRTExponentGridSum.gridMap p q (j, c) + ((q : ℕ) : ZMod (p * q)) := by
  have hsplit : (j + 1) % p * q + (j + 1) / p * (p * q) = (j + 1) * q := by
    calc (j + 1) % p * q + (j + 1) / p * (p * q)
        = ((j + 1) % p + p * ((j + 1) / p)) * q := by ring
      _ = (j + 1) * q := by rw [Nat.mod_add_div]
  have hz : (((j + 1) / p * (p * q) : ℕ) : ZMod (p * q)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have hmain : (((j + 1) % p * q : ℕ) : ZMod (p * q))
      = (((j + 1) * q : ℕ) : ZMod (p * q)) := by
    rw [← hsplit, Nat.cast_add, hz, add_zero]
  show (((j + 1) % p * q + c * p : ℕ) : ZMod (p * q))
      = ((j * q + c * p : ℕ) : ZMod (p * q)) + ((q : ℕ) : ZMod (p * q))
  rw [Nat.cast_add, Nat.cast_add, hmain]
  push_cast
  ring

/-! ## From fiber geometry to coset closure -/

/-- **Equal columns give `+p`-closure.**  This is the pure CRT bookkeeping half of the
squarefree de Bruijn proof: if every column fiber of the exponent grid is the same
subset of `[0,p)`, then moving one step in the second CRT coordinate keeps the exponent
inside `S`, i.e. `S` is a union of full `μ_q`-packets. -/
lemma closed_add_p_of_equal_fibers {p q : ℕ} (hppos : 0 < p) (hqpos : 0 < q)
    (hcop : Nat.Coprime p q) {S : Finset (ZMod (p * q))} {I : Finset (ℕ × ℕ)}
    (hmemI : ∀ x : ℕ × ℕ, x ∈ I ↔
      x ∈ Finset.range p ×ˢ Finset.range q ∧ CRTExponentGridSum.gridMap p q x ∈ S)
    (hall : ∀ c < q, ∀ c' < q, fiberSet p I c = fiberSet p I c') :
    ∀ e ∈ S, e + ((p : ℕ) : ZMod (p * q)) ∈ S := by
  intro e he
  obtain ⟨⟨j, c⟩, hx, hxe⟩ := CRTExponentGridSum.gridMap_surj hppos hqpos hcop e
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
  have hxI : (j, c) ∈ I := (hmemI (j, c)).mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx.1, Finset.mem_range.mpr hx.2⟩,
      hxe ▸ he⟩
  have hjcol : j ∈ fiberSet p I c := mem_fiberSet.mpr ⟨hx.1, hxI⟩
  have hceq : fiberSet p I c = fiberSet p I ((c + 1) % q) :=
    hall c hx.2 _ (Nat.mod_lt _ hqpos)
  have hxI' : (j, (c + 1) % q) ∈ I := (mem_fiberSet.mp (hceq ▸ hjcol)).2
  have hS' : CRTExponentGridSum.gridMap p q (j, (c + 1) % q) ∈ S :=
    ((hmemI _).mp hxI').2
  rw [← hxe, ← gridMap_snd_succ]
  exact hS'

/-- **Empty/full columns give `+q`-closure.**  Once every column fiber is either empty
or all of `[0,p)`, any occupied exponent lies in a full vertical packet, so stepping in
the first CRT coordinate keeps the exponent inside `S`. -/
lemma closed_add_q_of_empty_or_full_fibers {p q : ℕ} (hppos : 0 < p) (hqpos : 0 < q)
    (hcop : Nat.Coprime p q) {S : Finset (ZMod (p * q))} {I : Finset (ℕ × ℕ)}
    (hmemI : ∀ x : ℕ × ℕ, x ∈ I ↔
      x ∈ Finset.range p ×ˢ Finset.range q ∧ CRTExponentGridSum.gridMap p q x ∈ S)
    (hef : ∀ c < q, fiberSet p I c = ∅ ∨ fiberSet p I c = Finset.range p) :
    ∀ e ∈ S, e + ((q : ℕ) : ZMod (p * q)) ∈ S := by
  intro e he
  obtain ⟨⟨j, c⟩, hx, hxe⟩ := CRTExponentGridSum.gridMap_surj hppos hqpos hcop e
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
  have hxI : (j, c) ∈ I := (hmemI (j, c)).mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx.1, Finset.mem_range.mpr hx.2⟩,
      hxe ▸ he⟩
  have hjcol : j ∈ fiberSet p I c := mem_fiberSet.mpr ⟨hx.1, hxI⟩
  have hfull : fiberSet p I c = Finset.range p := by
    rcases hef c hx.2 with h | h
    · rw [h] at hjcol
      exact absurd hjcol (Finset.notMem_empty j)
    · exact h
  have hj' : (j + 1) % p ∈ fiberSet p I c := by
    rw [hfull]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hppos)
  have hxI' : ((j + 1) % p, c) ∈ I := (mem_fiberSet.mp hj').2
  have hS' : CRTExponentGridSum.gridMap p q ((j + 1) % p, c) ∈ S :=
    ((hmemI _).mp hxI').2
  rw [← hxe, ← gridMap_fst_succ]
  exact hS'

/-! ## The headline -/

/-- **De Bruijn step (3) at the squarefree two-prime level — pure-type disjoint
packets.**  For distinct primes `p ≠ q` and a primitive `(p·q)`-th root of unity `ζ`
in a characteristic-zero field, every exponent subset `S ⊆ ZMod (p·q)` with vanishing
indicator sum `Σ_{e∈S} ζ^e = 0` is closed under `e ↦ e + p` (a disjoint union of
rotated full μ_q-packets) or closed under `e ↦ e + q` (a disjoint union of rotated
full μ_p-packets).

Mechanism: the CRT grid sum (`CRTExponentGridSum.subset_sum_eq_grid_double_sum`)
vanishes, so by the unconditional fiber slice
(`CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers` at `a = b = 1`) ALL fiber sums
are equal; the prime indicator dichotomy then forces all fiber sets equal (closure
under `+p`) or, as soon as two differ, one of them is empty — making every fiber sum
zero and hence every fiber empty or full (closure under `+q`).

This is exactly the indicator instance of de Bruijn (Indag. Math. 1953) at `n = p·q`,
strengthened to PURE type (no mixtures — verified exhaustively by the probe at
`n = 6, 10, 15`; the prime-power extension is refuted there, so this scope is honest). -/
theorem debruijn_squarefree_two_prime {L : Type*} [Field L] [CharZero L]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p * q))
    {S : Finset (ZMod (p * q))} (hsum : ∑ e ∈ S, ζ ^ e.val = 0) :
    (∀ e ∈ S, e + ((p : ℕ) : ZMod (p * q)) ∈ S)
      ∨ (∀ e ∈ S, e + ((q : ℕ) : ZMod (p * q)) ∈ S) := by
  classical
  have hppos := hp.pos
  have hqpos := hq.pos
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hnpos : 0 < p * q := Nat.mul_pos hppos hqpos
  have hξ : IsPrimitiveRoot (ζ ^ q) p := hζ.pow hnpos (mul_comm p q)
  have hη : IsPrimitiveRoot (ζ ^ p) q := hζ.pow hnpos rfl
  set I : Finset (ℕ × ℕ) := CRTExponentGridSum.gridSet p q S with hIdef
  have hgrid : ∑ x ∈ I, (ζ ^ q) ^ x.1 * (ζ ^ p) ^ x.2 = 0 := by
    rw [hIdef,
      ← CRTExponentGridSum.subset_sum_eq_grid_double_sum hppos hqpos hcop
        hζ.pow_eq_one S]
    exact hsum
  have hξ1 : IsPrimitiveRoot (ζ ^ q) (p ^ 1) := by rw [pow_one]; exact hξ
  have hη1 : IsPrimitiveRoot (ζ ^ p) (q ^ 1) := by rw [pow_one]; exact hη
  have hI1 : I ⊆ Finset.range (p ^ 1) ×ˢ Finset.range (q ^ 1) := by
    simp only [pow_one]
    exact CRTExponentGridSum.gridSet_subset p q S
  -- all fibers are equal (b = 1: the μ_q-shift invariance compares every pair)
  have hfib : ∀ c < q, ∀ c' < q,
      (∑ j ∈ Finset.range p, if (j, c) ∈ I then (ζ ^ q) ^ j else 0)
        = ∑ j ∈ Finset.range p, if (j, c') ∈ I then (ζ ^ q) ^ j else 0 := by
    intro c hc c' hc'
    have h := CRTPacketMinpoly.crt_fiber_slice_coprimePrimePowers (a := 1) (b := 1)
      hp hq hpq one_pos hξ1 hη1 I hI1 hgrid (i := c) (i' := c') (s := 0) hc hc'
      (by norm_num)
    simpa using h
  -- the prime dichotomy on every fiber pair
  have hdich : ∀ c < q, ∀ c' < q,
      fiberSet p I c = fiberSet p I c'
        ∨ (fiberSet p I c = Finset.range p ∧ fiberSet p I c' = ∅)
        ∨ (fiberSet p I c = ∅ ∧ fiberSet p I c' = Finset.range p) := by
    intro c hc c' hc'
    refine equal_indicator_sums_dichotomy hp hξ (fiberSet_subset p I c)
      (fiberSet_subset p I c') ?_
    rw [sum_fiberSet, sum_fiberSet]
    exact hfib c hc c' hc'
  -- membership bookkeeping for the grid set
  have hmemI : ∀ x : ℕ × ℕ, x ∈ I ↔
      x ∈ Finset.range p ×ˢ Finset.range q ∧ CRTExponentGridSum.gridMap p q x ∈ S := by
    intro x
    rw [hIdef, CRTExponentGridSum.gridSet, Finset.mem_filter]
  rcases equal_fibers_or_empty_full_of_pairwise_dichotomy hdich with hall | hef
  · -- all fibers equal as sets: S is closed under `+p`
    left
    exact closed_add_p_of_equal_fibers hppos hqpos hcop hmemI hall
  · -- otherwise every fiber is empty/full, so S is closed under `+q`
    right
    exact closed_add_q_of_empty_or_full_fibers hppos hqpos hcop hmemI hef

/-! ## Non-vacuity witnesses

The headline fired at a genuine vanishing subset: `n = 2·3 = 6`, `ζ = exp(2πi/6) ∈ ℂ`,
`S = {0, 3}` (a rotated full μ₂-packet: `ζ⁰ + ζ³ = 1 + (−1) = 0`).  The disjunction is
decided to the RIGHT branch and the LEFT branch genuinely fails (kernel-checked), so
the theorem's content at this point is exactly "S is a union of μ₂-cosets". -/

/-- The witness subset is closed under `+3` (it IS a full μ₂-packet)… -/
example : ∀ e ∈ ({0, 3} : Finset (ZMod (2 * 3))),
    e + ((3 : ℕ) : ZMod (2 * 3)) ∈ ({0, 3} : Finset (ZMod (2 * 3))) := by decide

/-- …and NOT closed under `+2` — the disjunction below is decided, not vacuous. -/
example : ¬ ∀ e ∈ ({0, 3} : Finset (ZMod (2 * 3))),
    e + ((2 : ℕ) : ZMod (2 * 3)) ∈ ({0, 3} : Finset (ZMod (2 * 3))) := by decide

/-- The headline fired end-to-end at `ℂ`, `n = 6`, `S = {0, 3}`: a genuine nonempty
vanishing subset sum, every hypothesis discharged. -/
example :
    (∀ e ∈ ({0, 3} : Finset (ZMod (2 * 3))),
        e + ((2 : ℕ) : ZMod (2 * 3)) ∈ ({0, 3} : Finset (ZMod (2 * 3))))
      ∨ (∀ e ∈ ({0, 3} : Finset (ZMod (2 * 3))),
        e + ((3 : ℕ) : ZMod (2 * 3)) ∈ ({0, 3} : Finset (ZMod (2 * 3)))) := by
  have hζ6 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 6)) (2 * 3) := by
    have h := Complex.isPrimitiveRoot_exp 6 (by norm_num)
    norm_num at h
    exact h
  have hpow6 : (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ (2 * 3) = 1 :=
    hζ6.pow_eq_one
  have hpow3 : (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3 = -1 := by
    have hsq : (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3
        * (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3 = 1 := by
      rw [show (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3
          * (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3
          = (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ (2 * 3) from by ring]
      exact hpow6
    have hne1 : (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ 3 ≠ 1 := by
      intro hcon
      have hdvd := hζ6.dvd_of_pow_eq_one 3 hcon
      norm_num at hdvd
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h hne1
    · exact h
  have hval0 : ((0 : ZMod (2 * 3)).val) = 0 := rfl
  have hval3 : ((3 : ZMod (2 * 3)).val) = 3 := rfl
  have hne03 : (0 : ZMod (2 * 3)) ∉ ({3} : Finset (ZMod (2 * 3))) := by decide
  have hsum : ∑ e ∈ ({0, 3} : Finset (ZMod (2 * 3))),
      (Complex.exp (2 * Real.pi * Complex.I / 6)) ^ e.val = 0 := by
    rw [show ({0, 3} : Finset (ZMod (2 * 3)))
        = insert 0 ({3} : Finset (ZMod (2 * 3))) from rfl,
      Finset.sum_insert hne03, Finset.sum_singleton, hval0, hval3, pow_zero, hpow3]
    ring
  exact debruijn_squarefree_two_prime Nat.prime_two Nat.prime_three (by norm_num)
    hζ6 hsum

end DeBruijnIndicatorDisjointness

#print axioms DeBruijnIndicatorDisjointness.coeffs_all_eq_of_vanishing_prime
#print axioms DeBruijnIndicatorDisjointness.equal_indicator_sums_dichotomy
#print axioms DeBruijnIndicatorDisjointness.vanishing_indicator_empty_or_full
#print axioms DeBruijnIndicatorDisjointness.equal_fibers_or_empty_full_of_pairwise_dichotomy
#print axioms DeBruijnIndicatorDisjointness.gridMap_snd_succ
#print axioms DeBruijnIndicatorDisjointness.gridMap_fst_succ
#print axioms DeBruijnIndicatorDisjointness.closed_add_p_of_equal_fibers
#print axioms DeBruijnIndicatorDisjointness.closed_add_q_of_empty_or_full_fibers
#print axioms DeBruijnIndicatorDisjointness.debruijn_squarefree_two_prime
