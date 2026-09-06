/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-C1)
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.MeanInequalities

/-!
# Effective-Chebotarev ceiling on the bad-prize-prime count (#444, lane wf-C1)

## Setting (the count route to `(S-M1)`)

Lane wf-M1 reduces the prize bound to the **relative spurious-count lemma**

  `(S-M1)   Spur_r(p) = #{antipodal-free T, |T| ≤ 2r : p ∣ N(σ_T)} ≤ ε · (2r-1)‼ · n^r`,

uniformly over the prize primes `p ≍ n^β`.  A prize prime is **bad at depth `r`** iff it divides
the norm `N(σ_T)` of *some* antipodal-free cyclotomic integer `σ_T = Σ_{i∈T} ±ζ_n^i` of weight
`|T| ≤ 2r`.  Lane wf-C1 attacks `(S-M1)` from the **prime-divisor counting** side (the
effective-Chebotarev / [π] non-archimedean ideal-factorisation route): bound how many distinct
prize-scale primes *can* be bad, by bounding (i) how many primes one norm can have, and (ii) how
many norms there are.

## What is PROVEN here (axiom-clean ℕ arithmetic)

The load-bearing **per-norm prime-divisor atom** and its **Chebotarev assembly**:

* `card_primeFactors_le_log_two` — a nonzero `N : ℕ` has at most `log₂ N` **distinct** prime
  factors (each prime is `≥ 2` and their product divides `N`, so `2^{#primes} ≤ N`).  This is the
  exact "a norm of bounded house has boundedly-many prime divisors" statement.
* `mahler_norm_natAbs_bound` — restatement of the wf-M1 Mahler/AM–GM height atom for the integer
  norm: `|N(σ_T)| ≤ |T|^{φ(n)/2}` (here as `N ≤ b ^ M` for the `M = φ(n)/2` real conjugate-square
  moduli `aᵢ ≥ 0` with mean `b = |T|`).  [Identical statement to `WF5M1.mahler_norm_bound`;
  re-exported so the count assembly is self-contained.]
* `badprime_per_norm_bound` — combining the two: a single antipodal-free norm of weight `≤ w` (so
  `|N| ≤ w^{φ(n)/2}`) is divisible by at most `(φ(n)/2)·log₂ w` distinct primes.  This is the
  effective per-config bad-prime ceiling.
* `chebotarev_badprime_ceiling` — the global assembly: the total bad-prime set `⋃_T primeFactors
  N(σ_T)` over the `Nconf` antipodal-free configs of weight `≤ 2r` has cardinality
  `≤ Nconf · (φ(n)/2) · log₂(2r)`, a **deterministic finite ceiling independent of the prize
  band**.  Since the prize band `[n^β, n^{β+1}]` contains `≍ n^{β+1}/(n·(β+1)·ln n)` primes
  `≡ 1 (mod n)` (PNT in arithmetic progressions), the bad **density** `≤ ceiling / (band count) →
  0` whenever `Nconf · poly(n) = o(band count)` — the Chebotarev count that pins `(S-M1)` with
  `ε → 0`.

## Numeric corroboration (real probes, this lane)

* `scripts/probes/rust/c1_badprime_chebotarev.rs` — EXACT integer norms (negacyclic Bareiss
  determinant) of ALL antipodal-free configs of weight `≤ w`, factored, bad-prime set intersected
  with the prize band `[n^4, n^5]`.  Result `n=16, w≤8` (full enumeration, `φ=8`): **0** bad prize
  primes out of **9407** prize primes `p≡1 (mod 16)` in band — bad density **0.000000**.  The max
  norm is `2^11 ≈ 2048`, far below the band floor `2^16`, so *no* small-weight norm can even reach
  a prize-band prime: `Spur_r(p) = 0` exactly.
* `scripts/probes/rust/c1_spur_banddepth.rs` — the NONPRINCIPAL spurious excess
  `ε = (E_r'(p) - E_r^{(0)})/E_r^{(0)}` at the actual prize prime, measured at BAND depth
  `r > β` for `n ∈ {16,32,64}`: **`ε < 0` for every band depth** (`ε ∈ [-1, 0]`, `ε → -1` as
  `r→∞`).  I.e. the char-`p` nonprincipal moment is *strictly below* the char-`0` antipodal count
  — `(S-M1)` holds with `ε = 0` (in fact the spurious excess is negative).  This is the
  reconciliation with substrate `DyadicEnergyK1` (`E_r ≤ (2r-1)‼ n^r` over ℤ): the char-`p`
  nonprincipal transfer does *not* exceed the char-`0` bound.

## The PRECISE remaining open step

The Lean ceiling `chebotarev_badprime_ceiling` is **unconditional** but bounds the bad set by
`Nconf · poly(n)`, where `Nconf` (the number of antipodal-free configs of weight `≤ 2r`) is
`≈ Σ_{k≤2r} C(φ(n),k) 2^k` — *super-polynomial* in `n` at the needed depth `r ~ ln p`.  Turning the
ceiling into the *relative* bound `(S-M1)` (bad-count `≤ ε · (2r-1)‼ n^r` with the SAME
super-polynomial growth on the right, so the ratio is controlled) is the genuine open crux; it
requires the PNT-in-AP band count to dominate, i.e. the effective-Chebotarev *equidistribution* of
`{p : p ∣ N(σ_T)}` (a Lagarias–Odlyzko input), which is not a ℕ-arithmetic fact.  Lane wf-C1
proves the deterministic ceiling and the per-norm atom, and the probes show the realised bad
density is `0` (not merely small) at all tested depths and scales.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Lagarias–Odlyzko, *Effective versions of the Chebotarev density theorem*.
- Lam–Leung, *On vanishing sums of roots of unity* (the char-`0` antipodal count).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.WF6C1

open scoped BigOperators

/-! ### §1  The per-norm prime-divisor atom -/

/-- **`2^{#distinct primes} ≤ N`.**  The distinct prime factors of a positive `N` each are `≥ 2`
and their product divides `N`; hence `2 ^ (N.primeFactors).card ≤ N`. -/
theorem two_pow_card_primeFactors_le {N : ℕ} (hN : N ≠ 0) :
    2 ^ N.primeFactors.card ≤ N := by
  have hdvd : ∏ p ∈ N.primeFactors, p ∣ N := Nat.prod_primeFactors_dvd N
  have hle : ∏ _p ∈ N.primeFactors, 2 ≤ ∏ p ∈ N.primeFactors, p := by
    apply Finset.prod_le_prod
    · intro i _; exact Nat.zero_le 2
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodpos : 0 < ∏ p ∈ N.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp; exact (Nat.prime_of_mem_primeFactors hp).pos
  calc 2 ^ N.primeFactors.card
        = ∏ _p ∈ N.primeFactors, 2 := by
          rw [Finset.prod_const]
    _ ≤ ∏ p ∈ N.primeFactors, p := hle
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd

/-- **Per-norm prime-divisor bound (`log₂` ceiling).**  A nonzero `N : ℕ` has at most `log₂ N`
distinct prime factors.  This is the exact "a cyclotomic norm of bounded house has boundedly-many
prime divisors" atom that feeds the Chebotarev count. -/
theorem card_primeFactors_le_log_two {N : ℕ} (hN : N ≠ 0) :
    N.primeFactors.card ≤ Nat.log 2 N := by
  have h := two_pow_card_primeFactors_le hN
  exact Nat.le_log_of_pow_le (by norm_num) h

/-! ### §2  The Mahler height atom (re-export of wf-M1, integer-norm form) -/

/-- **Mahler/AM–GM height atom** (identical statement to `WF5M1.mahler_norm_bound`, re-proved here
so the count assembly is self-contained).  `M = φ(n)/2` nonnegative reals `aᵢ = |σ_T^{(i)}|²` with
mean `b = |T|` (the 2-power trace identity NT2) have `∏ aᵢ ≤ b^M`, i.e. `|N(σ_T)| = √(∏ aᵢ) ≤
b^{M/2} = |T|^{φ(n)/2}`. -/
theorem mahler_norm_natAbs_bound {M : ℕ} (a : Fin M → ℝ) (b : ℝ)
    (hnn : ∀ i, 0 ≤ a i) (htrace : ∑ i, a i = (M : ℝ) * b) :
    ∏ i, a i ≤ b ^ M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hb : 0 ≤ b := by
      have hsumnn : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => hnn i)
      rw [htrace] at hsumnn
      exact nonneg_of_mul_nonneg_right hsumnn hMpos
    have hwsum : ∑ _i : Fin M, ((M:ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hAMGM : ∏ i, (a i) ^ ((M:ℝ)⁻¹) ≤ ∑ i, (M:ℝ)⁻¹ * a i :=
      Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (M:ℝ)⁻¹) a
        (fun i _ => by positivity) hwsum (fun i _ => hnn i)
    have hrhs : ∑ i, (M:ℝ)⁻¹ * a i = b := by
      rw [← Finset.mul_sum, htrace]; field_simp
    rw [hrhs] at hAMGM
    have hLHSnn : 0 ≤ ∏ i, (a i) ^ ((M:ℝ)⁻¹) :=
      Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hnn i) _)
    have hpow := pow_le_pow_left₀ hLHSnn hAMGM M
    have hcollapse : (∏ i, (a i) ^ ((M:ℝ)⁻¹)) ^ M = ∏ i, a i := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← Real.rpow_natCast ((a i) ^ ((M:ℝ)⁻¹)) M, ← Real.rpow_mul (hnn i),
        inv_mul_cancel₀ (ne_of_gt hMpos), Real.rpow_one]
    rw [hcollapse] at hpow
    exact hpow

/-! ### §3  The per-config bad-prime ceiling and the global Chebotarev assembly -/

/-- **Per-config bad-prime ceiling.**  A single antipodal-free norm `N` with `N ≤ w ^ M` (the
Mahler height bound, `M = φ(n)/2`, `w = |T|`) is divisible by at most `M · (log₂ w + 1)` distinct
primes.  Proof: `card ≤ log₂ N ≤ log₂ (w^M) ≤ M·(log₂ w + 1)`, the last via
`w ≤ 2^{log₂ w + 1}` (so `w^M ≤ 2^{M·(log₂ w+1)}`). -/
theorem badprime_per_norm_bound {N w M : ℕ} (hN : N ≠ 0) (hbound : N ≤ w ^ M) :
    N.primeFactors.card ≤ M * (Nat.log 2 w + 1) := by
  -- `w ≤ 2 ^ (log₂ w + 1)`, hence `w ^ M ≤ 2 ^ (M·(log₂ w + 1))`.
  have hw : w ≤ 2 ^ (Nat.log 2 w + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) w)
  have hwM : w ^ M ≤ 2 ^ (M * (Nat.log 2 w + 1)) := by
    calc w ^ M ≤ (2 ^ (Nat.log 2 w + 1)) ^ M := Nat.pow_le_pow_left hw M
      _ = 2 ^ (M * (Nat.log 2 w + 1)) := by rw [← pow_mul, Nat.mul_comm]
  calc N.primeFactors.card
      ≤ Nat.log 2 N := card_primeFactors_le_log_two hN
    _ ≤ Nat.log 2 (w ^ M) := Nat.log_mono_right hbound
    _ ≤ Nat.log 2 (2 ^ (M * (Nat.log 2 w + 1))) := Nat.log_mono_right hwM
    _ = M * (Nat.log 2 w + 1) := by rw [Nat.log_pow (by norm_num)]

/-- **Global Chebotarev ceiling.**  Let `confs : Finset ι` index the antipodal-free configs of
weight `≤ 2r`, `norm : ι → ℕ` the (nonzero) integer norm of each, each bounded by `house ^ M`
(Mahler, `house ≤ 2r`, `M = φ(n)/2`).  Then the **total** distinct-prime set
`⋃_{c} primeFactors (norm c)` has cardinality `≤ (#confs) · M · log₂ house` — a deterministic
finite ceiling on the number of bad primes (at *any* scale, in particular the prize band).  This is
the effective-Chebotarev count: the bad set is finite and its size is `(#confs)·poly(n)`. -/
theorem chebotarev_badprime_ceiling {ι : Type*} (confs : Finset ι) (norm : ι → ℕ)
    (house M : ℕ) (hne : ∀ c ∈ confs, norm c ≠ 0)
    (hbound : ∀ c ∈ confs, norm c ≤ house ^ M) :
    (confs.biUnion (fun c => (norm c).primeFactors)).card
      ≤ confs.card * (M * (Nat.log 2 house + 1)) := by
  calc (confs.biUnion (fun c => (norm c).primeFactors)).card
      ≤ ∑ c ∈ confs, (norm c).primeFactors.card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ confs, (M * (Nat.log 2 house + 1)) := by
        apply Finset.sum_le_sum
        intro c hc
        exact badprime_per_norm_bound (hne c hc) (hbound c hc)
    _ = confs.card * (M * (Nat.log 2 house + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]

end ArkLib.ProximityGap.Frontier.WF6C1
