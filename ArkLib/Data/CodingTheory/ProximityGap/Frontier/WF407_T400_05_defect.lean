/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# The `e₂=0` mod-`q` defect is carrier-finite (Proximity Prize #407, thread T400-05-defect)

This file formalizes, **axiom-clean**, the *controllability* half of the `e₂=0` mod-`q`
additive-energy defect (`k_D`) that thread T400-05-defect measures directly at small `n`.

## Background (the measured object)

For a `w`-subset `S ⊆ μ_n` (`n = 2^μ`) the prize-relevant count is
`N(n,w; F) = #{ distinct e₁(S) : e₂(S) = 0, e₁(S) ≠ 0 }`. Its char-0 value is the
`Θ(n^{s_max})` combinatorial core (`issue400-…-singles-decomposition`, `s_max = μ−1`). Over
`F_q` (`q ≡ 1 mod n`) the count changes by the **mod-`q` defect**
`defect(q) = N(F_q) − N(char0)`, which decomposes (probe `sweep_A09_modq_defect.py`,
KB `deltastar-407-e2zero-modq-defect.md`) into

* **DROP** (saturation: char-0 `e₁` values collide mod `q`), and
* **RISE** (halo carriers: sets with `e₂(S) ≠ 0` in char 0 but `e₂(S) = 0 mod q`).

The **carrier-onset law** (measured exact at `n=16,w=6`): a set `S` is a halo carrier mod `q`
**iff** `q ∣ N(α)`, `α := e₂(S) ∈ ℤ[ζ_n]`, `N(α) = Res(Φ_n, α)` the cyclotomic field norm.
`α` is a signed sum of `C(w,2)` roots of unity, so by the archimedean keystone
(`CyclotomicNormDefectThreshold.natAbs_resultant_cyclotomic_le_bound`)
`|N(α)| ≤ C(w,2)^{φ(n)}`.

## The content of this file

The carrier-onset law makes the **set of carrier primes a divisor set of finitely many
nonzero bounded integers**, hence finite, with an explicit ceiling. We isolate the elementary
order/finiteness skeleton (the `ℤ[ζ_n]` geometry is supplied by `CyclotomicNormDefectThreshold`
and enters here only through the named bound `|N(α)| ≤ B` and divisibility `q ∣ N(α)`):

* `carrierPrime_le_bound` — a carrier prime is `≤ B = C(w,2)^{φ(n)}` (the per-α version is the
  in-tree `CyclotomicNormDefectThreshold.prime_le_of_balanced_tuple`; here we state it directly
  on the norm value and assemble the *set-level* conclusion).
* `carrierPrimes_finite` — over a **finite** family of carrier seeds (the finitely many distinct
  `α = e₂(S)` over `w`-subsets), the set of all carrier primes is **finite**: it injects into the
  union of divisor sets of the (finitely many, nonzero) norms, each a finite set bounded by `B`.
* `carrierPrimes_subset_Icc` — every carrier prime lies in `Finset.Icc 1 B` (the sharp
  enclosing interval), giving a concrete finite enclosure.

## Honesty contract (what this does and does NOT prove)

This proves **controllability at fixed `(n,w)`**: only finitely many primes can be carriers, all
bounded by the explicit archimedean ceiling `B = C(w,2)^{φ(n)}` — the carrier-prime set is a
finite divisor set, *not* a positive-density spray. This is the rigorous form of the measured
"the carrier-prime set is finite, bounded by `max|N|`".

It does **NOT** close the prize. The bound `B = C(w,2)^{φ(n)}` is the generic archimedean
ceiling; in the prize regime `φ(n) = n/2 = 2^{31}` it is astronomically `> q ≈ n·2^{128}`, so a
**worst-case adversary can always pick `q ∣ N(α)` for the largest realizable norm** — the
worst-case-over-`q` lever the grand challenge demands. Controllability at fixed `(n,w)` does NOT
imply a uniform-in-`q` defect bound; that is the open NVM/ideal-SVP wall (face 3 of the open
core; `arklib-407-largesieve-avgq-refuted`, `…-equidistribution-defect…`). Verdict for the
thread: **walled** — the `e₂=0` defect is a direct, concrete measurement of the same
`k_D` mod-`q` defect, controllable per fixed `(n,w)` but NOT uniformly over the adversary's
choice of `q`.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.WF407_T400_05_defect

/-- **A carrier prime is bounded by the norm ceiling.** If `N` is the (nonzero) cyclotomic field
norm of `α = e₂(S)` with `|N| ≤ B` (e.g. `B = C(w,2)^{φ(n)}` by the archimedean keystone), and a
prime `q` is a carrier (`q ∣ N`), then `q ≤ B`. This is the set-level restatement of the in-tree
per-`α` `prime_le_of_balanced_tuple`, stated on the norm value. -/
theorem carrierPrime_le_bound {N : ℤ} {q B : ℕ}
    (hN0 : N ≠ 0) (hbound : N.natAbs ≤ B) (hdvd : (q : ℤ) ∣ N) :
    q ≤ B := by
  have hNabs : (q : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
  have hqdvd : q ∣ N.natAbs := by exact_mod_cast hNabs
  have hNpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN0
  exact le_trans (Nat.le_of_dvd hNpos hqdvd) hbound

/-- **The carrier-prime set lies in `Icc 1 B`.** Every carrier prime `q` (a prime dividing the
nonzero norm `N`, `|N| ≤ B`) lies in the finite interval `Finset.Icc 1 B`. -/
theorem carrierPrime_mem_Icc {N : ℤ} {q B : ℕ}
    (hq : 1 ≤ q) (hN0 : N ≠ 0) (hbound : N.natAbs ≤ B) (hdvd : (q : ℤ) ∣ N) :
    q ∈ Finset.Icc 1 B :=
  Finset.mem_Icc.mpr ⟨hq, carrierPrime_le_bound hN0 hbound hdvd⟩

/-- **Carrier-prime finiteness (set form).** Let `seeds : Finset ι` index the finitely many
distinct carrier seeds `α : ι → ℤ` (the distinct `e₂(S)` over `w`-subsets), each nonzero with
`|α i| ≤ B`. Then the set of all carrier primes
`{ q | ∃ i ∈ seeds, (q:ℤ) ∣ α i }` is **finite**.

This is the controllability statement: over the finite seed family the carrier primes form a
finite divisor set bounded by `B = C(w,2)^{φ(n)}`. -/
theorem carrierPrimes_finite {ι : Type*} (seeds : Finset ι) (α : ι → ℤ) (B : ℕ)
    (hα0 : ∀ i ∈ seeds, α i ≠ 0) (hbound : ∀ i ∈ seeds, (α i).natAbs ≤ B) :
    {q : ℕ | ∃ i ∈ seeds, (q : ℤ) ∣ α i}.Finite := by
  -- The carrier-prime set is a subset of the finite interval `Icc 1 B`.
  apply Set.Finite.subset (Finset.Icc 1 B).finite_toSet
  rintro q ⟨i, hi, hdvd⟩
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · -- `q = 0 ∣ α i` would force `α i = 0`, contradicting `hα0`.
    simp only [Nat.cast_zero, zero_dvd_iff] at hdvd
    exact absurd hdvd (hα0 i hi)
  · exact carrierPrime_mem_Icc (Nat.one_le_iff_ne_zero.mpr hqpos.ne')
      (hα0 i hi) (hbound i hi) hdvd

/-- **Carrier-prime finiteness (`Finset` enclosure).** The carrier-prime set is contained in the
explicit finite enclosure `Finset.Icc 1 B`. A constructive companion to `carrierPrimes_finite`
that exposes the *concrete* enclosing interval `[1, C(w,2)^{φ(n)}]`. -/
theorem carrierPrimes_subset_Icc {ι : Type*} (seeds : Finset ι) (α : ι → ℤ) (B : ℕ)
    (hα0 : ∀ i ∈ seeds, α i ≠ 0) (hbound : ∀ i ∈ seeds, (α i).natAbs ≤ B) :
    {q : ℕ | ∃ i ∈ seeds, (q : ℤ) ∣ α i} ⊆ ↑(Finset.Icc 1 B) := by
  rintro q ⟨i, hi, hdvd⟩
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · simp only [Nat.cast_zero, zero_dvd_iff] at hdvd
    exact absurd hdvd (hα0 i hi)
  · exact Finset.mem_coe.mpr
      (carrierPrime_mem_Icc (Nat.one_le_iff_ne_zero.mpr hqpos.ne')
        (hα0 i hi) (hbound i hi) hdvd)

end ArkLib.ProximityGap.WF407_T400_05_defect

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.WF407_T400_05_defect
#print axioms carrierPrime_le_bound
#print axioms carrierPrime_mem_Icc
#print axioms carrierPrimes_finite
#print axioms carrierPrimes_subset_Icc
end AxiomAudit
