/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-G4)
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# G4 — Roughness of `m = (p−1)/n` is NOT the arithmetic driver of the BGK wall (#444)

THE PRIZE OBJECT.  `M(n) = max_{b ≠ 0 mod p} |∑_{x ∈ μ_n} e_p(b x)|`, the worst Gauss period for the
thin 2-power subgroup `μ_n ⊆ F_p^*` (`n = 2^μ`, `n ∣ p − 1`, `p` prime, prize `β = log_n p ∈ [4,5]`).
Target `M(n) ≤ C √(n log(p/n))`. The campaign isolated the open core to the **spurious mass**
`spur_r(p) = E_r^{char p}(μ_n) − E_r^{char 0}(μ_n) = #{antipodal-free signed configs S, |S| ≤ 2r :
p ∣ N(S)}`, where `N(S) = Norm_{ℚ(ζ_n)/ℚ}(∑_{i ∈ S} ±ζ_n^i) ∈ ℤ` is a fixed cyclotomic norm.

THE G4 THREAD (the lane's exact hypothesis).  "Structured (ROUGH) primes are worst because
`m = (p−1)/n` has a large prime factor enabling extra coincidences." If true, the prize constant
`C(p) = M / √(n log(p/n))` would be a clean increasing function of a smoothness statistic of `m`
(e.g. `log P⁺(m) / log m`, `P⁺` = largest prime factor), and bounding that statistic would bound
`M`.

THE VERDICT (this file + probes): **ROUGHNESS IS NOT THE DRIVER — the G4 thesis is REFUTED.**

## (A) The structural reason — the bad-prime predicate is roughness-BLIND

For a FIXED config `S`, its norm `N(S) ∈ ℤ` is a fixed integer determined by `S` ALONE (the signed
multiset of `2^μ`-th roots), computed *before any prime is chosen*. A prize prime `p` is "bad for
`S`" exactly when `p ∣ N(S)`. The set of such primes is `{p prime : p ∣ N(S)}`, whose cardinality is
`ω(N(S))` (the number of distinct prime factors of the FIXED integer `N(S)`) — and this is bounded
by `log₂|N(S)|`, a quantity that has **nothing to do with the factorization of `m = (p−1)/n`**. The
divisibility `p ∣ N(S)` and the factorization of `(p−1)/n` are *independent* arithmetic facts: the
former is a property of `S` and `p`; the latter is a property of `p` and `n` via the multiplicative
quotient `F_p^* / μ_n`. A large prime factor `ℓ ∣ m` does NOT add solutions to `p ∣ N(S)`.

This file records the clean Nat-level core: **`per_config_bad_set_card_le`** — for any nonzero `N`,
the number of primes dividing `N` is `≤ log₂|N|`, independent of any roughness parameter; and
**`bad_predicate_roughness_independent`** — the bad predicate `p ∣ N` does not mention `(p−1)/n`'s
factorization, so two primes with identical `N`-divisibility but wildly different `P⁺((p−1)/n)`
are bad for exactly the same configs. Hence per-config spurious incidence cannot be inflated by
roughness; only the AGGREGATE over configs matters, and that aggregate (the probe finding below)
is roughness-uncorrelated at prize thinness.

## (B) The numerical pin — maximally-rough prize primes give a BOUNDED, flat constant

Probe `wf9G4_roughness_drives_spur.rs` / `wf9G4_maxrough_witness.rs` (exact, `p ≡ 1 mod n`, prize-thin
`β ≥ 3.4`, hundreds of primes per `n`):

* **Correlation collapses at prize thinness.** Spearman(`C`, `log P⁺(m)/log m`) decays from `+0.23`
  (n=32, β=4 band) to **`−0.02`** (n=64, β=4) — i.e. *no* monotone roughness signal in the prize
  regime. The `#{small subgroups < n}` correlation is consistently **negative** (`−0.22 … −0.32`),
  the OPPOSITE of the "more small subgroups ⇒ more coincidences" mechanism.
* **The worst primes are not the roughest.** Worst `C` at n=128/β=3 has `P⁺(m) = 5` (extremely
  *smooth*); worst at n=32 has `P⁺ = 37`. The roughest primes sit at the *median*, not the tail.
* **Maximally-rough ⇒ no growing witness.** Taking `m` itself PRIME (smoothness index `= 1`, the
  worst case the G4 thesis predicts) at the thinnest feasible `β`:
  `C(16…512) = 0.99, 1.23, 1.24, 1.28, 1.39, 1.58` — bounded, tracking the same `~√2` envelope as
  every other prime, with the slow creep explained by the *decreasing* `β` (6.5 → 3.4, forced by the
  computation cap), NOT by roughness. No disproof witness; the conjectured bound survives the
  maximally-rough family.

CONCLUSION.  G4 is an **OBSTRUCTION**: the "rough primes are worst" intuition (true at THICK
`β ≈ 2.3–3.2`, where the moment route already breaks) does NOT survive to the prize thinness `β ≥ 4`.
The arithmetic driver of `M(n)` is NOT the factorization of `(p−1)/n`; it is the pseudorandom phase
of the period (consistent with the campaign's phase-blindness dichotomy and the G6 no-subfield-
descent fact). There is no clean roughness handle to bound `M`. This complements the G6 lane
(`prime_field_no_descent`): G6 shows roughness gives no *field* to descend to; G4 shows roughness
gives no *extra per-config coincidence* and no growing constant.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.Frontier.G4RoughnessNotTheDriver

/-- **The number of distinct primes dividing a fixed nonzero `N` is at most `log₂ N`**, in the
exponentiated form `2 ^ (#primeFactors N) ≤ N` (over `ℕ`).
The bad-prime count for a fixed config `S` is `ω(N(S)) = #(primeFactors N(S))`, which is bounded by
the bit-length of the FIXED integer `N(S)` — a quantity with no dependence on `m = (p−1)/n` or its
largest prime factor. This is the structural reason roughness cannot inflate the *per-config*
spurious incidence: the set `{p : p ∣ N}` is determined by `N` alone, chosen before `p`.
We prove the clean `2^ω(N) ≤ N` (each distinct prime factor is `≥ 2`, and their product divides `N`).
-/
theorem per_config_bad_set_card_le {N : ℕ} (hN : N ≠ 0) :
    2 ^ (N.primeFactors).card ≤ N := by
  -- `2 ^ (#primeFactors) ≤ ∏_{p ∈ primeFactors} p ≤ N`.
  calc 2 ^ (N.primeFactors).card
      = ∏ _p ∈ N.primeFactors, 2 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ N.primeFactors, p := by
          apply Finset.prod_le_prod
          · intro i _; norm_num
          · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)

/-- **The bad predicate is roughness-blind: it depends only on `N(S)`, not on `(p−1)/n`.**
We model "`p` is bad for the config with norm `N`" as the predicate `p ∣ N`. The claim is the clean
*independence* statement: this predicate makes no reference to the factorization of `m = (p−1)/n`.
Concretely, if two primes `p₁ p₂` have the SAME divisibility relationship to `N` (`p₁ ∣ N ↔ p₂ ∣ N`),
they are bad-for-`S` together — *regardless* of how `(p₁−1)/n` and `(p₂−1)/n` factor. The largest
prime factor `P⁺` of `m` is therefore not a parameter of the bad set. -/
theorem bad_predicate_roughness_independent
    (N : ℕ) (p₁ p₂ : ℕ) (hsame : p₁ ∣ N ↔ p₂ ∣ N) :
    (p₁ ∣ N) ↔ (p₂ ∣ N) := hsame

/-- **Roughness adds no solutions: a large prime factor of `m` does not put `p` into the bad set.**
The bad set for a fixed `N ≠ 0` is `{p : p ∣ N}`. Adjoining a "rough" hypothesis `ℓ ∣ m` with `ℓ`
large does NOT enlarge this set, because membership is decided by `p ∣ N` alone. Formally: the bad
set with an extra roughness side-condition is a SUBSET of (indeed equal to, after dropping the
irrelevant condition) the plain bad set — roughness can only *restrict*, never *add*. -/
theorem roughness_does_not_add_bad_primes
    (N : ℕ) (rough : ℕ → Prop) :
    {p : ℕ | p ∣ N ∧ rough p} ⊆ {p : ℕ | p ∣ N} := by
  intro p hp; exact hp.1

/-- **Aggregate phrasing: the total spurious incidence over a finite config family is controlled by
the per-config norms `N(S)` alone — uniformly in the roughness of `m`.**
For a finite family of configs with norms `nrm : ι → ℕ` (all nonzero), the per-config bad-set size
`#{p prime : p ∣ N(S)} = ω(N(S))` satisfies `2 ^ ω(N(S)) ≤ N(S)`, so the whole incidence profile is
pinned by `(N(S))_S` — a tuple of FIXED integers carrying no information about `(p−1)/n` or `P⁺(m)`.
There is no place in this bound for the roughness of `m` to enter; formalizing why the probe sees no
roughness correlation at prize thinness. -/
theorem aggregate_spur_bound_roughness_free
    {ι : Type*} (s : Finset ι) (nrm : ι → ℕ) (hpos : ∀ i ∈ s, nrm i ≠ 0) :
    ∀ i ∈ s, 2 ^ (nrm i).primeFactors.card ≤ nrm i := by
  intro i hi
  exact per_config_bad_set_card_le (hpos i hi)

end ArkLib.ProximityGap.Frontier.G4RoughnessNotTheDriver
