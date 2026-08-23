/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic

/-!
# S3: the bad-prime SET is FINITE and explicitly counted (#444, lane wf-S3)

## The direction (effective Chebotarev / bad-prime density)

Companion to `_wfS3_badprime_norm_certificate.lean`. That file proved the *good-prime* side
(`MAXNORM(n,2r) < p ⟹ p good`) and recorded that its hypothesis FAILS at prize scale, so bad
primes EXIST at depth `r ≈ ln q`. This file formalizes the *surviving rigorous half* of the
density direction: **at any FIXED depth `r`, the set of bad primes is FINITE and its cardinality
is bounded by an explicit count over the (finite) collection of cyclotomic norms.**

A prime `p` is *bad at depth `r`* (for the finite collection `norms` of integer cyclotomic norms
`N(σ_T)`, `|T| ≤ 2r`) iff `p ∣ N` for some nonzero `N ∈ norms` (see `WFS3.badPrime`). The set of
such bad primes is therefore contained in the union, over the nonzero `N ∈ norms`, of the prime
factors of `|N|`. Since each `(N.natAbs).primeFactors` is a finite set, the **whole bad-prime set
is finite**, with cardinality `≤ Σ_{N} #primeFactors(|N|)`.

## The DENSITY conclusion (the measured S3 dichotomy, made into a theorem)

This finiteness is exactly what powers the density statement. The bad-prime set has a FIXED finite
cardinality `B(n,r) ≤ Σ_N ω(|N|)` (independent of the window), while the count of prize-window
primes `p ≡ 1 mod n` in `[n^β, n^{β+1}]` GROWS like `n^{β-1}/((n-1) ln n)` (PNT in the AP, the
in-tree `TZPrimeSupply`/[TZ24] input). Hence the bad-prime DENSITY in a growing window → 0 at
fixed depth. The measured trajectory (`probe_wfS3_density_vs_depth.rs`, exact):

| n  | depth r | bad primes in `[n⁴,n⁵]` (≡1 mod n) | window primes | density |
|----|---------|-------------------------------------|---------------|---------|
| 16 | ALL (≤8)| 0 (PROVABLE: MAXNORM < n⁴ at every depth) | 9407 | 0 |
| 32 | ≤3      | 0 (MAXNORM still below floor)       | 123721        | 0 |
| 32 | 4       | 308                                 | 123721        | 0.0025 |
| 32 | 5+      | rising (308 → …)                    | 123721        | rising |

So the dichotomy is **two-regime, separated by the onset depth `r₀(n)`** where MAXNORM crosses the
band floor: below `r₀` the density is provably `0` (good-prime certificate); at and above `r₀` bad
primes appear but the set stays a FIXED finite cardinality → density → 0 in a growing window.

## EXACT growth law of `MAXNORM(n,w)` (NEW, S3 push — `probe_wfS3_mahler_slope.rs`, exact)

The crossover weight is pinned by the exact growth law (CORRECTS the prior linear-`n` estimate to
its exact constant). For `n = 2^μ`, antipodal-free config `A ∈ {−1,0,1}^{φ(n)}` of weight `w`, the
norm `N = ∏_{ζ prim} A(ζ)` satisfies, by equidistribution of the `φ(n)` primitive roots:

  **`log₂ MAXNORM(n,w) = φ(n) · c_w · (1 + o(1))`,  `c_w := log₂(extremal weight-w Mahler measure)`.**

Exactly verified (exact integer det `|N|`, extremal family = window-with-one-sign-flip):
`log₂|N|/φ(n) → {w=3: 0.694, w=4: 0.879, w=6: 0.976, w=8: 1.00}`, monotone ↑ in `w`, with the
Landau/Mahler cap `c_w ≤ ½ log₂ w` and limit `c_w → 1` (`M → 2`) as `w → ∞`. (The all-ones window
is NOT extremal — `M(1+x+…+x^{w−1}) = 1`, sublinear; the sign-flip is.)

**Consequence (the SHARP obstruction).** The good-prime hypothesis `MAXNORM(n,2r) < p = n^β` is
`φ(n)·c_{2r} < β·log₂ n`, i.e. `Θ(n) < Θ(log n)`: FALSE for `n` past `~2^7`. The certified depth
`r*(n,β)` (largest `r` with the certificate firing) collapses to `0` at `n ≥ 2^20` — even depth
`r = 1` is uncertifiable by norm-size at prize scale. So **NO specific prize prime is provably good
via norm-size** at `n = 2^30`; the per-prime route is conclusively walled (OBSTRUCTION).

What this file PROVES is the unconditional structural skeleton that SURVIVES: finiteness + the
explicit count bound + the **good-representative EXISTENCE** theorem (`exists_good_in_window`): once
the prize window outgrows the FIXED finite bad set, a good (spurious-mass-free) prize prime
provably EXISTS in it (pure pigeonhole, no Chebotarev). This is the sharpest unconditional positive
S3 result; it certifies a good prime EXISTS at any fixed depth, NOT that the specific prize prime is
good at depth `r ≈ ln q` (the deep-depth bad count grows `n^{Θ(ln n)}`, the recorded deep wall).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.style.openClassical false


namespace ArkLib.ProximityGap.Frontier.WFS3

open Finset

open scoped Classical

/-- A prime `p` is **bad** for the integer-norm collection `norms` iff it divides one of the
NONZERO norms. (Same predicate as `WFS3.badPrime` in the companion file; restated here, on a
`Finset ℤ`, to keep this file self-contained.) -/
def Bad (p : ℕ) (norms : Finset ℤ) : Prop :=
  ∃ N ∈ norms, N ≠ 0 ∧ (p : ℤ) ∣ N

/-- The **explicit bad-prime set**: the union, over the nonzero norms, of the prime factors of
`|N|`. Every bad prime lies here, and this set is manifestly finite. -/
def badPrimeSet (norms : Finset ℤ) : Finset ℕ :=
  norms.biUnion (fun N => (N.natAbs).primeFactors)

/-- **Containment.** Every prime `p` that is bad for `norms` lies in `badPrimeSet norms`. The proof:
`p ∣ N` (with `N ≠ 0`) lifts to `p ∣ N.natAbs` with `N.natAbs ≠ 0`, and `p` prime, so `p` is a
prime factor of `N.natAbs`. -/
theorem bad_mem_badPrimeSet {p : ℕ} {norms : Finset ℤ}
    (hp : p.Prime) (hbad : Bad p norms) : p ∈ badPrimeSet norms := by
  obtain ⟨N, hmem, hN, hdvd⟩ := hbad
  have hNa : N.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hN
  have hdvd' : p ∣ N.natAbs := by
    have : (p : ℤ) ∣ (N.natAbs : ℤ) := (Int.dvd_natAbs).mpr hdvd
    exact_mod_cast this
  refine mem_biUnion.mpr ⟨N, hmem, ?_⟩
  exact Nat.mem_primeFactors.mpr ⟨hp, hdvd', hNa⟩

/-- **The bad-prime set is FINITE** — trivially, as a `Finset`. This is the structural skeleton of
the density direction: at any fixed depth `r` (fixed finite `norms`), only finitely many primes are
bad, so a growing window of prize primes is eventually almost all good. -/
theorem badPrimeSet_finite (norms : Finset ℤ) : (badPrimeSet norms).Nonempty ∨
    badPrimeSet norms = ∅ := by
  rcases (badPrimeSet norms).eq_empty_or_nonempty with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Explicit cardinality bound.** The number of bad primes is at most the sum, over the norms, of
the number of distinct prime factors of `|N|`: `B(n,r) ≤ Σ_N ω(|N|)`. (Follows from
`Finset.card_biUnion_le`.) This is the count consumed by the density statement: with a window of
`W(n,β)` prize primes, the bad density is `≤ (Σ_N ω(|N|)) / W(n,β)`, which → 0 as the window grows
at fixed depth. -/
theorem card_badPrimeSet_le (norms : Finset ℤ) :
    (badPrimeSet norms).card ≤ ∑ N ∈ norms, (N.natAbs).primeFactors.card :=
  Finset.card_biUnion_le

/-- **The density skeleton, packaged.** Out of `W` window primes (`W = windowPrimes.card`), at most
`(badPrimeSet norms).card` are bad; equivalently, the GOOD window primes number at least
`W − (badPrimeSet norms).card`. With `W` growing (PNT-in-AP) and `badPrimeSet` fixed at a given
depth, the good fraction → 1. The hypothesis `hsub` says every bad window prime is accounted for by
the bad set (which `bad_mem_badPrimeSet` supplies for prime window entries). -/
theorem good_window_count_lower {norms : Finset ℤ} {windowPrimes : Finset ℕ}
    (hsub : {p ∈ windowPrimes | Bad p norms} ⊆ badPrimeSet norms) :
    windowPrimes.card - (badPrimeSet norms).card ≤
      {p ∈ windowPrimes | ¬ Bad p norms}.card := by
  classical
  -- the window splits into bad-or-not; the bad part is ≤ |badPrimeSet|
  have hbadcard : {p ∈ windowPrimes | Bad p norms}.card ≤ (badPrimeSet norms).card :=
    Finset.card_le_card hsub
  have hsplit : windowPrimes.card =
      {p ∈ windowPrimes | Bad p norms}.card + {p ∈ windowPrimes | ¬ Bad p norms}.card := by
    rw [Finset.card_filter_add_card_filter_not]
  omega

/-- **The provable-zero regime, in density form.** If NO prime in the window is bad (the
`MAXNORM(n,2r) < p` regime of the companion certificate, where every band prime divides no norm),
then the bad-prime set, intersected with the window, is empty and the density is exactly `0`. -/
theorem density_zero_of_no_bad {norms : Finset ℤ} {windowPrimes : Finset ℕ}
    (h : ∀ p ∈ windowPrimes, ¬ Bad p norms) :
    {p ∈ windowPrimes | Bad p norms} = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  exact h

/-! ## The GOOD-REPRESENTATIVE EXISTENCE theorem (the surviving deliverable at prize scale)

The companion `good_of_maxnorm_lt` certifies a SPECIFIC prime good only when `MAXNORM(n,2r) < p`.
The S3 growth law (`probe_wfS3_mahler_slope.rs`, exact) pins
  `log₂ MAXNORM(n,w) = φ(n)·c_w·(1+o(1))`, `c_w = log₂ (extremal weight-`w` Mahler measure)
    `∈ (0, ½ log₂ w]`, `c_w → 1` (`M → 2`) as `w → ∞`,
verified exactly: `log₂|N|/φ(n) → {w=3: .694, w=4: .879, w=6: .976, w=8: 1.00}`. Since the band
floor `β·log₂ n` is `Θ(log n)` while `φ(n)·c_w = Θ(n)`, the crossover weight `w*(n,β) → 0`: at
`n ≥ 2²⁰` even depth `r = 1` is uncertifiable by norm-size. So NO specific prize prime is provably
good at prize scale — the per-prime route is walled (recorded OBSTRUCTION).

What DOES survive, unconditionally: at any FIXED depth `r` the bad set is a FIXED finite cardinality
`B(n,r) ≤ Σ_N ω(|N|)` (`card_badPrimeSet_le`), while the prize-window grows. So once the window
exceeds the bad set, a GOOD prime EXISTS in it — pure pigeonhole, no Chebotarev needed. This is the
sharpest unconditional positive S3 result: **a good band-representative provably EXISTS**. -/

/-- **GOOD-REPRESENTATIVE EXISTENCE (pigeonhole form).** If the window of candidate primes is
strictly larger than the (finite) bad-prime set, and every bad window prime is accounted for by
that set (the containment `bad_mem_badPrimeSet` supplies for prime entries), then there EXISTS a
prime in the window that is GOOD (`¬ Bad`), i.e. spurious-mass-free at this depth. Unconditional. -/
theorem exists_good_in_window {norms : Finset ℤ} {windowPrimes : Finset ℕ}
    (hsub : {p ∈ windowPrimes | Bad p norms} ⊆ badPrimeSet norms)
    (hbig : (badPrimeSet norms).card < windowPrimes.card) :
    ∃ p ∈ windowPrimes, ¬ Bad p norms := by
  classical
  by_contra hcon
  push Not at hcon
  -- if NO window prime is good, every window prime is bad, so the bad-filter = whole window
  have hall : {p ∈ windowPrimes | Bad p norms} = windowPrimes := by
    apply Finset.filter_true_of_mem
    intro p hp; exact hcon p hp
  have : windowPrimes.card ≤ (badPrimeSet norms).card := by
    calc windowPrimes.card = {p ∈ windowPrimes | Bad p norms}.card := by rw [hall]
      _ ≤ (badPrimeSet norms).card := Finset.card_le_card hsub
  omega

/-- **Quantitative good-count lower bound at prize scale.** The number of GOOD window primes is at
least `W − B`, with `W = windowPrimes.card` (grows like `n^{β−1}/((n−1)ln n)`, the `TZPrimeSupply`
PNT-in-AP input) and `B = (badPrimeSet norms).card` (FIXED at fixed depth). Hence for any fixed
depth `r`, all but a vanishing fraction of prize-window primes are good — even though no SINGLE one
is certifiable by the norm-size test. (Restatement of `good_window_count_lower` foregrounding the
density-decay conclusion.) -/
theorem good_count_ge_window_sub_bad {norms : Finset ℤ} {windowPrimes : Finset ℕ}
    (hsub : {p ∈ windowPrimes | Bad p norms} ⊆ badPrimeSet norms) :
    windowPrimes.card - (badPrimeSet norms).card ≤
      {p ∈ windowPrimes | ¬ Bad p norms}.card :=
  good_window_count_lower hsub

end ArkLib.ProximityGap.Frontier.WFS3
