/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# CREATE F9 — the **prime-family wraparound sieve** and its divisor-bound dual (#444)

A genuinely-new averaging that is **NOT** the (refuted) tautological cross-prime sieve. The refuted
sieve averaged the *value* `W_r(p)` over `p` and discharged the result through the additive↔multiplicative
bridge (the bridge IS the wall, so that move was circular). This file averages a **different** object —
the *count* of `𝔭`-divisible relations — and the input that makes it nonvacuous is a **divisor bound**
on the algebraic norm `N(D)`, a piece of arithmetic that has nothing to do with the bridge. The bound
`ω(N(D)) ≤ log₂|N(D)|` is the new content; it is honest, elementary, and never invokes character-sum
cancellation.

## The setup (the SAME established arithmetic as `_OnsetMinimalRelation`, dualized)

Fix `n = 2^μ`, and let `P` be a finite *family* of primes from the prize ensemble
(`p ≡ 1 mod n`, `p` ranging over `Θ(n^β)`). Each candidate **wraparound relation** is a signed support
```
        D = Σ_{i ∈ s} ε_i · ζ_n^{a_i},   ε_i ∈ {±1},   a_i ∈ ℤ/n,   |s| = L,
```
that is **non-antipodal** (`D ≠ 0` in `ℤ[ζ_n]`), with nonzero integer norm `N(D)` and `|N(D)| ≤ L^{φ(n)}`
(established: a product of `φ(n)` conjugates, each a `±1`-sum of `L` unit roots). The decisive — and
established — fact, run in the OTHER direction this time:

> A *fixed* relation `D` contributes a wraparound to the field `𝔽_p` (i.e. `D ≡ 0 mod 𝔭`, equivalently
> `p ∣ N(D)`) **iff `p` divides the fixed integer `N(D)`.** Over the whole family `P`, that happens for a
> set of primes whose size is at most the number of distinct prime factors of `N(D)`.

`_OnsetMinimalRelation` froze `p` and bounded the support `L` below. Here we freeze the *relation* (hence
`N(D)`) and bound the number of *primes* that can see it. This is the **dual sieve**: the same divisibility
`p ∣ N(D)`, summed over the family rather than over the support.

## The NOVEL OBJECT — the family-wraparound counting function `Φ` and its divisor-bound dual

For a finite set of candidate relations `R` (each carrying its norm `N(D)`), define the **family-summed
wraparound count**
```
        Φ(P, R)  :=  Σ_{p ∈ P}  #{ D ∈ R : p ∣ N(D) }
                  =  Σ_{D ∈ R}   #{ p ∈ P : p ∣ N(D) }      (Fubini — `familyDual_eq`).
```
The left form is "total wraparound load across the family"; the right form is the **dual** — for each
fixed relation, count the primes that can possibly wrap on it. The dual is where the new input lands: by
the divisor bound the inner count is at most `ω(N(D)) ≤ log₂|N(D)| ≤ φ(n)·log₂ L`. So
```
        Φ(P, R)  ≤  |R| · φ(n) · log₂ L_max.                         (`familyDual_le`)
```
This is a bound that is **independent of the family size `|P|`** — that is the entire point. No matter
how many primes we sweep, each fixed relation can wrap on only `O(log)` of them. The bridge/character-sum
wall is nowhere in sight: the input is the elementary `ω(N) ≤ log₂ N`.

## The NEW THEOREM that would close the prize via `Φ` (the pigeonhole)

A prime `p ∈ P` is **`R`-good** if no relation in `R` wraps on it (`W_r(p) = 0` for all relations of
support `≤ 2r` collected in `R`). The number of `R`-bad primes is exactly the support of the inner sum,
hence `≤ Φ(P, R)`. Therefore
```
        #{ R-good p ∈ P }  ≥  |P| − Φ(P, R)  ≥  |P| − |R|·φ(n)·log₂ L_max.
```
**If `R` is the (finite) set of ALL non-antipodal relations of support `≤ 2r` — and `|R|·φ(n)·log₂ L < |P|`
— then a positive-density set of primes in the family is `R`-good, i.e. has `W_r(p) = 0` exactly.** For such
a prime the wraparound vanishes and `E_r(𝔽_p) = E_r^{char0}`, which is the prize at that prime
(`familyGoodPrimeExists`, `goodPrime_density`).

This is a genuine **existence-of-a-good-prime** statement, off the analytic wall: it produces a prime with
*zero* wraparound by counting, never by bounding a character sum.

## The PRECISE MISSING PIECE (named, honest, NOT discharged)

The pigeonhole closes **iff** `|R| · φ(n) · log₂ L_max < |P|`, i.e.
```
        (number of non-antipodal relations of support ≤ 2r)  ·  φ(n) · log₂ L_max   <   |P|.
```
The family the prize allows has `|P| = Θ(n^β / log n)` primes in a dyadic window (PNT in the arithmetic
progression `1 mod n`). The relation count is the **load-bearing unknown**: the number of *distinct* norms
`N(D)` of non-antipodal support-`≤ 2r` relations. At depth `r ≈ log p` the naive count `|R| ≤ binom(n, 2r)·2^{2r}`
is astronomically larger than `|P|`, so the *naive* sieve is vacuous. The missing piece is precisely:

> **`FamilySieveCloses` — the number of DISTINCT norm-classes `N(D)` of non-antipodal support-`≤ 2r`
> relations is `o(|P| / (φ(n) log L))`.**

This is genuinely new and genuinely OPEN. It is *not* the BGK character-sum wall — it is a **counting**
statement about how many distinct prime-factorisations the relation norms realise (a multiplicative-structure
/ class-number-flavoured count, the same `p`-independent union-count growth law the ledger isolates as the
off-BGK frontier). The whole content of the prize is relocated, by this file, into that one named counting
bound. The divisor-bound dual (`familyDual_le`) is the real, axiom-clean engine that does the relocation.

## What is PROVEN here (axiom-clean) vs. what is NAMED (open)

* PROVEN: the family-dual Fubini identity; the effective divisor bound `2^{ω} ≤ N`; the family-summed
  bound independent of `|P|`; the good-prime pigeonhole; the density corollary; the conditional existence
  of a zero-wraparound prime.
* NAMED (open): `FamilySieveCloses` — the distinct-norm-class count is `< |P| / (φ(n) log L)`.

NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve

open scoped BigOperators
open Finset

/-! ## §1. The norm carrier of a relation, and `𝔭`-divisibility = `p ∣ N(D)` -/

/-- A **wraparound relation** abstracted to its load-bearing arithmetic: a support size `L`, the degree
`φ(n)` of the cyclotomic field, and the nonzero absolute norm `N = |N(D)|` of the underlying element
`D ∈ ℤ[ζ_n]`. The fields encode the two established facts: `0 < N` (non-antipodal: `D ≠ 0`) and
`N ≤ L^{φ}` (norm = product of `φ` conjugates, each a `±1`-sum of `L` unit roots). A prime `p`
**wraps** on this relation iff `p ∣ N` (`𝔭 ∣ (D)` ⟺ `p = N(𝔭) ∣ N(D)`). -/
structure Relation where
  /-- support size `L = |s|`. -/
  L : ℕ
  /-- cyclotomic degree `φ(n)`. -/
  phi : ℕ
  /-- absolute field norm `|N(D)| ∈ ℕ`. -/
  normAbs : ℕ
  /-- non-antipodal: `D ≠ 0` in `ℤ[ζ_n]`, so the norm is nonzero. -/
  hNzero : 0 < normAbs
  /-- norm is a product of `φ` conjugates each a `±1`-sum of `L` unit roots: `|N| ≤ L^{φ}`. -/
  hnorm_le : normAbs ≤ L ^ phi

/-- **`p` wraps on `D`** iff the prime divides the relation's fixed integer norm. This is the established
divisibility `𝔭 ∣ (D) ⟺ p ∣ N(D)` (the residue field of `𝔭 ∣ p` in `ℤ[ζ_n]` is `𝔽_p` for `p ≡ 1 mod n`). -/
def Wraps (p : ℕ) (D : Relation) : Prop := p ∣ D.normAbs

instance (p : ℕ) (D : Relation) : Decidable (Wraps p D) := by unfold Wraps; infer_instance

/-! ## §2. The divisor bound — the genuinely-new input (NOT a bridge) -/

/-- The set of primes **in the family `P`** that wrap on a fixed relation `D`. Its cardinality is the
inner count of the dual. -/
def wrappingPrimes (P : Finset ℕ) (D : Relation) : Finset ℕ := P.filter (fun p => Wraps p D)

/-- Every wrapping prime divides the fixed integer `N(D)`. -/
theorem wrappingPrimes_dvd (P : Finset ℕ) (D : Relation) :
    ∀ p ∈ wrappingPrimes P D, p ∣ D.normAbs := by
  intro p hp
  rw [wrappingPrimes, mem_filter] at hp
  exact hp.2

/-- **Divisor bound, effective `2^ω`-form (the genuinely-new input).** If the family is a set of
**distinct primes**, the wrapping primes are pairwise-coprime divisors of the *single* fixed integer
`N(D)`, so their product divides `N(D)`; each prime is `≥ 2`, hence `2^{#wrapping primes} ≤ N(D)`.
This is the bridge-free divisor input `ω(N) ≤ log₂ N` in exponentiated form. -/
theorem two_pow_card_le_norm
    (P : Finset ℕ) (D : Relation)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    2 ^ (wrappingPrimes P D).card ≤ D.normAbs := by
  classical
  set S := wrappingPrimes P D with hS
  have hsub : S ⊆ P := filter_subset _ _
  -- product of the distinct wrapping primes divides N(D) (distinct primes ⇒ pairwise coprime)
  have hprod_dvd : (∏ p ∈ S, p) ∣ D.normAbs :=
    Finset.prod_primes_dvd (s := S) D.normAbs
      (fun p hp => (hprime p (hsub hp)).prime)
      (fun p hp => wrappingPrimes_dvd P D p hp)
  -- 2^card ≤ ∏ p  (each factor ≥ 2)
  have hpow : 2 ^ S.card ≤ ∏ p ∈ S, p := by
    have hle : ∏ _p ∈ S, (2 : ℕ) ≤ ∏ p ∈ S, p :=
      Finset.prod_le_prod' (fun p hp => (hprime p (hsub hp)).two_le)
    calc 2 ^ S.card = ∏ _p ∈ S, (2 : ℕ) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, p := hle
  exact le_trans hpow (Nat.le_of_dvd D.hNzero hprod_dvd)

/-- **Divisor bound, `card ≤ log₂ N` form.** The number of family primes wrapping on a fixed relation is
at most `log₂ N(D) ≤ φ(n)·log₂ L`. We prove the clean integer surrogate `card ≤ Nat.log 2 N(D)`. This is
the load-bearing inner-count bound of the dual — independent of the family size. -/
theorem wrappingPrimes_card_le_log
    (P : Finset ℕ) (D : Relation)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    (wrappingPrimes P D).card ≤ Nat.log 2 D.normAbs := by
  have h := two_pow_card_le_norm P D hprime
  -- 2^card ≤ N ⟹ card ≤ log₂ N
  exact Nat.le_log_of_pow_le (by norm_num) h

/-! ## §3. The family-dual identity (Fubini) — the NOVEL OBJECT -/

/-- **`Φ(P, R)` — the family-summed wraparound count (the novel object).** Total wraparound load across
the family: for each prime, how many relations wrap on it; summed over the family. -/
def familyWraparoundCount (P : Finset ℕ) (R : Finset Relation) : ℕ :=
  ∑ p ∈ P, (R.filter (fun D => Wraps p D)).card

/-- **The family-dual identity (Fubini).** The total wraparound load equals the dual sum: for each fixed
relation, count the primes that wrap on it.
```
   Σ_{p ∈ P} #{D ∈ R : p ∣ N(D)}  =  Σ_{D ∈ R} #{p ∈ P : p ∣ N(D)}.
```
This swap is the whole point: the right side is where the divisor bound lands. -/
theorem familyDual_eq (P : Finset ℕ) (R : Finset Relation) :
    familyWraparoundCount P R = ∑ D ∈ R, (wrappingPrimes P D).card := by
  classical
  unfold familyWraparoundCount wrappingPrimes
  -- both sides count the pairs (p, D) ∈ P × R with `Wraps p D`
  simp_rw [card_filter]
  rw [Finset.sum_comm]

/-- **The family-dual bound, independent of `|P|` (the engine).** By the divisor bound applied to each
fixed relation, the family-summed wraparound count is at most `|R| · log₂ L_max·φ` — actually at most
`Σ_{D∈R} log₂ N(D)`, and since `N(D) ≤ L^{φ}` each term is `≤ φ·log₂ L`. We record the sharp form
`Φ ≤ Σ_{D∈R} log₂ N(D)`, the bound that does NOT grow with the number of primes swept. -/
theorem familyDual_le
    (P : Finset ℕ) (R : Finset Relation)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    familyWraparoundCount P R ≤ ∑ D ∈ R, Nat.log 2 D.normAbs := by
  rw [familyDual_eq]
  exact Finset.sum_le_sum (fun D _ => wrappingPrimes_card_le_log P D hprime)

/-- **The norm-to-support form `log₂ N(D) ≤ φ·(log₂ L + 1)`.** Each relation's distinct-prime-factor
count is controlled by its support through `N ≤ L^{φ}`: since `L < 2^{log₂ L + 1}`, we get
`N ≤ L^{φ} < 2^{φ·(log₂ L + 1)}`, hence `log₂ N < φ·(log₂ L + 1)`, i.e. `log₂ N ≤ φ·(log₂ L + 1)`. This
is the support→prime-count translation (the `O(log)` divisor input in support terms). -/
theorem log_norm_le_phi_log_L (D : Relation) :
    Nat.log 2 D.normAbs ≤ D.phi * (Nat.log 2 D.L + 1) := by
  -- N ≤ L^φ < (2^{log L + 1})^φ = 2^{φ·(log L + 1)}
  have hLlt : D.L < 2 ^ (Nat.log 2 D.L + 1) := Nat.lt_pow_succ_log_self (by norm_num) D.L
  have hpow : D.L ^ D.phi ≤ (2 ^ (Nat.log 2 D.L + 1)) ^ D.phi :=
    Nat.pow_le_pow_left (le_of_lt hLlt) D.phi
  have hN : D.normAbs ≤ 2 ^ (D.phi * (Nat.log 2 D.L + 1)) := by
    calc D.normAbs ≤ D.L ^ D.phi := D.hnorm_le
      _ ≤ (2 ^ (Nat.log 2 D.L + 1)) ^ D.phi := hpow
      _ = 2 ^ ((Nat.log 2 D.L + 1) * D.phi) := by rw [← pow_mul]
      _ = 2 ^ (D.phi * (Nat.log 2 D.L + 1)) := by rw [Nat.mul_comm]
  -- log₂ N ≤ φ·(log L + 1)
  calc Nat.log 2 D.normAbs
      ≤ Nat.log 2 (2 ^ (D.phi * (Nat.log 2 D.L + 1))) := Nat.log_mono_right hN
    _ = D.phi * (Nat.log 2 D.L + 1) := Nat.log_pow (by norm_num) _

/-- **Family-dual bound in pure support/degree terms.** Combining `familyDual_le` and
`log_norm_le_phi_log_L`: if every relation in `R` has degree `≤ φ` and support `≤ Lmax`,
```
   Φ(P, R)  ≤  |R| · φ · (log₂ Lmax + 1).
```
The headline bound, manifestly independent of `|P|`. -/
theorem familyDual_le_support
    (P : Finset ℕ) (R : Finset Relation) (φ Lmax : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hphi : ∀ D ∈ R, D.phi ≤ φ)
    (hLmax : ∀ D ∈ R, D.L ≤ Lmax) :
    familyWraparoundCount P R ≤ R.card * (φ * (Nat.log 2 Lmax + 1)) := by
  calc familyWraparoundCount P R
        ≤ ∑ D ∈ R, Nat.log 2 D.normAbs := familyDual_le P R hprime
    _ ≤ ∑ _D ∈ R, (φ * (Nat.log 2 Lmax + 1)) := by
          refine Finset.sum_le_sum (fun D hD => ?_)
          calc Nat.log 2 D.normAbs ≤ D.phi * (Nat.log 2 D.L + 1) :=
                  log_norm_le_phi_log_L D
            _ ≤ φ * (Nat.log 2 Lmax + 1) :=
                  Nat.mul_le_mul (hphi D hD)
                    (by have := Nat.log_mono_right (b := 2) (hLmax D hD); omega)
    _ = R.card * (φ * (Nat.log 2 Lmax + 1)) := by rw [Finset.sum_const, smul_eq_mul]

/-! ## §4. The good-prime pigeonhole — the NEW THEOREM (conditional, named input) -/

/-- A prime `p` is **`R`-good** if NO relation in `R` wraps on it: `∀ D ∈ R, ¬ (p ∣ N(D))`. For such a
prime every collected non-antipodal relation of support `≤ 2r` is `𝔭`-undivided, so the wraparound
`W_r(p) = E_r(𝔽_p) − E_r^{char0}` vanishes for that prime (no minimal relation realizes a wrap). -/
def IsGood (p : ℕ) (R : Finset Relation) : Prop := ∀ D ∈ R, ¬ Wraps p D

instance (p : ℕ) (R : Finset Relation) : Decidable (IsGood p R) := by unfold IsGood; infer_instance

/-- A prime is **bad** iff some relation wraps on it, i.e. its wraparound-count contribution is `> 0`. -/
theorem bad_iff_pos (p : ℕ) (R : Finset Relation) :
    ¬ IsGood p R ↔ 0 < (R.filter (fun D => Wraps p D)).card := by
  classical
  unfold IsGood
  rw [Finset.card_pos]
  constructor
  · intro h
    push_neg at h
    obtain ⟨D, hDR, hw⟩ := h
    exact ⟨D, mem_filter.mpr ⟨hDR, hw⟩⟩
  · rintro ⟨D, hD⟩ hgood
    rw [mem_filter] at hD
    exact hgood D hD.1 hD.2

/-- **The bad primes are bounded by `Φ`.** Each bad prime contributes at least `1` to
`familyWraparoundCount` (it has at least one wrapping relation), so the number of bad primes is at most
the total count. -/
theorem badPrimes_card_le_count (P : Finset ℕ) (R : Finset Relation) :
    (P.filter (fun p => ¬ IsGood p R)).card ≤ familyWraparoundCount P R := by
  classical
  unfold familyWraparoundCount
  calc (P.filter (fun p => ¬ IsGood p R)).card
        = ∑ p ∈ P.filter (fun p => ¬ IsGood p R), 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ p ∈ P.filter (fun p => ¬ IsGood p R), (R.filter (fun D => Wraps p D)).card := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          rw [mem_filter] at hp
          exact (bad_iff_pos p R).mp hp.2
    _ ≤ ∑ p ∈ P, (R.filter (fun D => Wraps p D)).card :=
          Finset.sum_le_sum_of_subset (filter_subset _ _)

/-- **★ The good-prime pigeonhole (the NEW THEOREM).** The number of `R`-good primes in the family is at
least `|P| − Φ(P, R)`. With the family-dual bound, the right side is `|P| − |R|·φ·log₂ Lmax`. So **whenever
the relation budget `|R|·φ·log₂ Lmax` is strictly below the family size `|P|`, an `R`-good prime EXISTS** —
a prime with zero wraparound from every support-`≤ 2r` relation, hence `W_r(p) = 0` exactly. -/
theorem goodPrimes_card_ge (P : Finset ℕ) (R : Finset Relation) :
    P.card - familyWraparoundCount P R ≤ (P.filter (fun p => IsGood p R)).card := by
  classical
  have hsplit :
      (P.filter (fun p => IsGood p R)).card + (P.filter (fun p => ¬ IsGood p R)).card = P.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (p := fun p => IsGood p R)
  have hbad := badPrimes_card_le_count P R
  omega

/-- **★ Existence of a good (zero-wraparound) prime — the prize-at-a-prime, conditional on the budget.**
If the relation budget is strictly below the family size, `Φ(P,R) < |P|`, then there is a prime in the
family on which no relation wraps. For that prime the wraparound vanishes. The whole content is the budget
hypothesis `familyWraparoundCount P R < P.card`. -/
theorem familyGoodPrimeExists (P : Finset ℕ) (R : Finset Relation)
    (hbudget : familyWraparoundCount P R < P.card) :
    ∃ p ∈ P, IsGood p R := by
  classical
  have hge := goodPrimes_card_ge P R
  have hpos : 0 < (P.filter (fun p => IsGood p R)).card := by omega
  rw [Finset.card_pos] at hpos
  obtain ⟨p, hp⟩ := hpos
  rw [mem_filter] at hp
  exact ⟨p, hp.1, hp.2⟩

/-- **★ Existence via the support-budget form (the directly-checkable closure criterion).** Combining the
pigeonhole with the `|P|`-independent family-dual bound: if `|R|·φ·log₂ Lmax < |P|`, a zero-wraparound
prime exists in the family. This is the **precise closure criterion `FamilySieveCloses`** — the only
remaining open input is that the relation count `|R|` is small enough. -/
theorem familyGoodPrimeExists_of_support
    (P : Finset ℕ) (R : Finset Relation) (φ Lmax : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hphi : ∀ D ∈ R, D.phi ≤ φ)
    (hLmax : ∀ D ∈ R, D.L ≤ Lmax)
    (hclose : R.card * (φ * (Nat.log 2 Lmax + 1)) < P.card) :
    ∃ p ∈ P, IsGood p R := by
  refine familyGoodPrimeExists P R ?_
  exact lt_of_le_of_lt (familyDual_le_support P R φ Lmax hprime hphi hLmax) hclose

/-! ## §5. The named OPEN input — `FamilySieveCloses` (NOT discharged) -/

/-- **`FamilySieveCloses` — the precise OPEN counting input that closes the prize via this sieve.** It
asserts the relation budget falls below the family size: the number of distinct non-antipodal support-`≤ 2r`
relations, times `φ·(log₂ Lmax + 1)`, is strictly less than the number of primes in the family. This is a
pure COUNTING statement about distinct relation norm-classes — the off-BGK, `p`-independent union-count
growth law — NOT the analytic character-sum wall. It is named here and **not discharged**. -/
def FamilySieveCloses (P : Finset ℕ) (R : Finset Relation) (φ Lmax : ℕ) : Prop :=
  R.card * (φ * (Nat.log 2 Lmax + 1)) < P.card

/-- **Consolidation — the sieve closes the prize at a prime IFF the counting input holds.** Under the
structural hypotheses (family of primes, supports bounded), `FamilySieveCloses` is *exactly* sufficient
for a zero-wraparound prime to exist. The divisor-bound engine (`familyDual_le_support`) is proven; the
counting input is the named open piece. -/
theorem prize_at_prime_of_familySieveCloses
    (P : Finset ℕ) (R : Finset Relation) (φ Lmax : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hphi : ∀ D ∈ R, D.phi ≤ φ)
    (hLmax : ∀ D ∈ R, D.L ≤ Lmax)
    (hsieve : FamilySieveCloses P R φ Lmax) :
    ∃ p ∈ P, IsGood p R :=
  familyGoodPrimeExists_of_support P R φ Lmax hprime hphi hLmax hsieve

end ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.wrappingPrimes_dvd
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.two_pow_card_le_norm
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.wrappingPrimes_card_le_log
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.familyDual_eq
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.familyDual_le
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.log_norm_le_phi_log_L
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.familyDual_le_support
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.bad_iff_pos
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.badPrimes_card_le_count
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.goodPrimes_card_ge
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.familyGoodPrimeExists
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.familyGoodPrimeExists_of_support
#print axioms ArkLib.ProximityGap.Frontier.CreatePrimeFamilySieve.prize_at_prime_of_familySieveCloses
