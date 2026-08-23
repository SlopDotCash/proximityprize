/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Depth-4 norm-height finiteness of the D4-bad prime set (#466 lane F2)

The depth-4 face of the wraparound-excess scanner (`scripts/probes/probe_466_d4_scanner.py`,
run3: exhaustive `n = 32`, 13,319 window primes) DIVERGES from depth 3: the window
`[n⁴, 4n⁴]` contains `92` in-window K-bad primes (max `W₄ / K-margin` ratio `2.14`), where the
depth-3 face has none.  This file records the **unconditional finiteness backbone** that any
depth-4 divisor-structure theorem sits on: the norm-height cutoff.

## The norm-height cutoff (math sketch)

Let `μ_n ⊂ F_p^×` be the order-`n` subgroup, `n = 2^k`, `p ≡ 1 (mod n)`.  A depth-4 wraparound
event is a relation
`ζ^{a₁}+ζ^{a₂}+ζ^{a₃}+ζ^{a₄} ≡ ζ^{b₁}+ζ^{b₂}+ζ^{b₃}+ζ^{b₄}  (mod P)`
for a prime `P ∣ p` in `ℤ[ζ_n]` that does **not** already hold over `ℤ[ζ_n]` (i.e. `W₄` counts
exactly the sums that wrap around mod `p` without vanishing in characteristic 0).  The witness
`α = (Σ ζ^{aᵢ}) − (Σ ζ^{bᵢ}) ∈ ℤ[ζ_n]` is nonzero, `P ∣ α`, and every Galois conjugate `σ(α)`
is again a difference of two sums of four roots of unity, so `|σ(α)| ≤ 8 = 2·r` with `r = 4`.
Hence the algebraic norm satisfies `0 < |N(α)| = ∏_σ |σ(α)| ≤ 8^{φ(n)} = 8^{n/2}`, and
`p ∣ N(α)` forces `p ≤ |N(α)| ≤ 8^{n/2}`.  Therefore

`D4bad(n) ⊆ { p : p ≤ 8^{n/2} }`,   an unconditionally **finite** set.

At `n = 8` this is `8^4 = 4096 = n⁴`, so the whole window `[n⁴, 4n⁴]` is provably D4-clean —
matching the scan (`n = 8`: 0 exact-bad in window).  The point of lane F2 is that finiteness
alone does not settle the `n^{7/8}` bilinear route: at `n = 32` the cutoff `8^{16} ≈ 2.8·10¹⁴`
is far ABOVE the window, so it excludes no window prime — the good-prime supply needs the
finer *structure* of the in-window K-bad set (census: `probe_466_d4_structure.py`), not just
finiteness of the crude bad set.

## Census verdict — the `n^{7/8}` route is REFUTED (lane F2)

The point of finiteness was a hoped-for *divisor structure theorem* (analogous to the width-four
canonical resultant, `CanonicalWidthFourBadPrimeSet.lean`): if the in-window depth-4 K-bad set were
contained in the prime factors of ONE small norm-height integer, a Thorner-Zaman window would
outrun it and the `n^{7/8}` bilinear route would get free depth-4 good-prime supply.  The census
`scripts/probes/probe_466_d4_structure.py` (exhaustive `n = 32`, all 13,319 window primes;
anchor `W₄(65537,16) = +4480`) **REFUTES** this.  Of the 92 in-window K-bad primes:

* `0` are generalized-Fermat `p = b^{2^s}+1`;
* `0` have high 2-adic valuation (`v₂(p−1) ≥ 13`); the `v₂` histogram is
  `{5:47, 6:21, 7:18, 8:2, 9:3, 10:1}` — `47/92` sit at the MINIMAL forced `v₂ = 5`;
* the odd cofactor `(p−1)/2^{v₂}` is generic, frequently a single large prime;
* they span the WHOLE window `β = log_n p ∈ [4.005, 4.394]`, up to the top edge.

Clean generic countermodels (`p ≡ 1 mod 32`, `p−1 = 2⁵·(large prime)`, minimal structure, yet
K-bad): `p = 1391393 = 2⁵·43481` (43481 prime), `p = 2089889 = 2⁵·65309` (65309 prime, `β=4.20`),
`p = 1524449 = 2⁵·47639` (47639 prime), `p = 4102753 = 2⁵·3·42737` (`β=4.394`, top of window).
No fixed small integer collects these — there is NO depth-4 divisor structure theorem.  Hence the
`n^{7/8}` route's `T4 = O(n⁴)` free good-prime supply **does not exist**; the depth-4 K-badness is
an arithmetically-generic positive-density phenomenon.  (The `n^{8/9}` depth-3 route is unaffected:
depth 3 has NO in-window K-bad prime.)

## What is PROVEN here (axiom-clean)

* `d4NormHeightBound` — the explicit depth-4 cutoff `8^{n/2}`.
* `d4NormHeightBound_eight` — at `n = 8` it equals `n⁴ = 4096` (the provably-clean window).
* `d4Bad_finite` — the norm-height inclusion (given as the modular hypothesis) makes any
  D4-bad set FINITE (the crude bad set; unconditional finiteness backbone).
* `d4Bad_card_le_of_dvd_normHeightInteger` — the census-as-divisibility-gate form: if every
  D4-bad prime divides one fixed nonzero norm-height integer `H`, the D4-bad set has at most
  `H.primeFactors.card` elements.
* `card_le_of_d4GoodSupplyBudget` — the route's supply hypothesis at budget `m` forces the
  in-window K-bad set to have `≤ m` elements.  This is the exact lever the census DEFEATS: at
  `n = 32` the in-window K-bad set already has `92` generic elements with no shared small
  divisor, so no sub-window budget `m` can hold — `D4GoodSupplyBudget` is a named hypothesis the
  numerics REFUTE, not a theorem.

`D4NormHeightInclusion` and `D4GoodSupplyBudget` are deliberately-named hypotheses (the
algebraic-number-theory norm bound, resp. the refuted divisor-structure supply); neither is
asserted true here — per the project's residual convention.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.D4NormHeightFinite

open Finset

/-- Depth-4 norm-height cutoff: `(2r)^{φ(n)}` with `r = 4` (so `2r = 8`) and `φ(2^k) = n/2`.
Any prime supporting a genuine depth-4 wraparound (a `≡ 0 mod p` relation of `≤ 4`-root sums
that does not already vanish in characteristic 0) is `≤ d4NormHeightBound n`. -/
def d4NormHeightBound (n : ℕ) : ℕ := 8 ^ (n / 2)

/-- At `n = 8` the depth-4 cutoff is exactly `n⁴ = 4096`: the whole prize window `[n⁴, 4n⁴]` is
provably D4-clean, matching the exhaustive scan. -/
theorem d4NormHeightBound_eight : d4NormHeightBound 8 = 8 ^ 4 := rfl

/-- Sanity: the `n = 8` cutoff equals `n⁴`. -/
theorem d4NormHeightBound_eight_eq_pow_four : d4NormHeightBound 8 = 4096 := rfl

/-- The **norm-height inclusion**: every prime in the D4-bad set `S` is `≤ 8^{n/2}`.  This is the
named modular input carrying the archimedean norm bound (see the file header); it is not reproved
here. -/
def D4NormHeightInclusion (n : ℕ) (S : Set ℕ) : Prop :=
  ∀ p ∈ S, p ≤ d4NormHeightBound n

/-- **Finiteness of the D4-bad set from the norm-height cutoff.**  Given the norm-height
inclusion, the D4-bad prime set is finite (contained in the finite initial segment
`{p ≤ 8^{n/2}}`). -/
theorem d4Bad_finite {n : ℕ} {S : Set ℕ} (h : D4NormHeightInclusion n S) : S.Finite :=
  (Set.finite_Iic (d4NormHeightBound n)).subset (fun _ hp => h _ hp)

/-- The set of primes below the depth-4 cutoff is itself finite (the crude bad-set envelope). -/
theorem finite_setOf_le_d4NormHeightBound (n : ℕ) :
    {p : ℕ | p ≤ d4NormHeightBound n}.Finite :=
  Set.finite_Iic (d4NormHeightBound n)

/-- **Census-as-divisibility-gate.**  If every D4-bad prime (as a `Finset`) divides one fixed
nonzero norm-height integer `H`, then the D4-bad set has at most `H.primeFactors.card` elements.
This is the concrete integer-divisibility form of the structure question: it says the D4-bad set
is pinned by the prime factorization of a single arithmetic invariant (the product of the finitely
many depth-4 witness norms), exactly the shape of the width-four canonical resultant lane. -/
theorem d4Bad_card_le_of_dvd_normHeightInteger
    (P Bad : Finset ℕ) {H : ℕ} (hH : H ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime) (hBadSub : Bad ⊆ P)
    (hBadDvd : ∀ p ∈ Bad, p ∣ H) :
    Bad.card ≤ H.primeFactors.card := by
  classical
  have hsub : Bad ⊆ H.primeFactors := by
    intro p hpBad
    exact Nat.mem_primeFactors.mpr ⟨hprime p (hBadSub hpBad), hBadDvd p hpBad, hH⟩
  exact Finset.card_le_card hsub

/-- The **D4 good-supply budget** at cardinality `m` (the refuted route hypothesis): the in-window
depth-4 K-bad set `B` is contained in the prime factors of a single fixed nonzero norm-height
integer `H` with at most `m` prime divisors.  For the width-four canonical resultant lane `m` is
`O(φ(n)·n)` (`log₂` of the resultant), so a Thorner-Zaman window of larger supply beats it.  The
`n^{7/8}` bilinear route needed the analogous *small*-`m` bound at depth 4.

**Census verdict: this is FALSE at prize-relevant scale** — the exhaustive `n = 32` scan exhibits
`92` in-window K-bad primes that are arithmetically generic (minimal `v₂`, prime odd cofactors,
spread across the window), so no fixed small `H` collects them.  This `Prop` is a named
hypothesis, not a theorem; downstream MUST NOT assume it. -/
def D4GoodSupplyBudget (B : Finset ℕ) (m : ℕ) : Prop :=
  ∃ H : ℕ, H ≠ 0 ∧ H.primeFactors.card ≤ m ∧ (∀ p ∈ B, p ∣ H)

/-- If the (refuted) good-supply budget holds at `m`, the in-window K-bad set has `≤ m` elements.
This is the lever the census defeats: at `n = 32` the K-bad set already has `92` generic elements,
so `D4GoodSupplyBudget B m` fails for every sub-window `m`. -/
theorem card_le_of_d4GoodSupplyBudget {B : Finset ℕ} {m : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (h : D4GoodSupplyBudget B m) : B.card ≤ m := by
  obtain ⟨H, hH, hcard, hdvd⟩ := h
  exact (d4Bad_card_le_of_dvd_normHeightInteger B B hH hprime (le_refl B) hdvd).trans hcard

end ArkLib.ProximityGap.Frontier.D4NormHeightFinite

namespace ArkLib.ProximityGap.Frontier.D4NormHeightFinite

#print axioms d4NormHeightBound_eight
#print axioms d4Bad_finite
#print axioms finite_setOf_le_d4NormHeightBound
#print axioms d4Bad_card_le_of_dvd_normHeightInteger
#print axioms card_le_of_d4GoodSupplyBudget

end ArkLib.ProximityGap.Frontier.D4NormHeightFinite
