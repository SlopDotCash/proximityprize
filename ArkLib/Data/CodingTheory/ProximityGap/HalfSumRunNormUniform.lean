/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# The uniform-in-`n` run-sum cyclotomic norm closed form (#407 — Half-Sum Lemma, lane C)

This file closes the **uniform-in-`n` gap** of `HalfSumNormClosedForm.lean`.

`HalfSumNormClosedForm.lean` proves the closed form
`N_{K/ℚ}(1 + ζ + ⋯ + ζ^{n/2-1}) = 2^{n/2-1}` for the *single* all-ones half-sum (and its
rotation orbit) over a conductor-`n = 2^{m+1}` cyclotomic field. That is the base point of the
candidate-bad-prime norm ledger, but it is one subset sum per level `n`.

This file extends that to **every consecutive run** `1 + ζ + ⋯ + ζ^{L-1}`, of *any* length
`1 ≤ L < n`, with a closed form that is **uniform in `n`**: the norm depends ONLY on the
`2`-adic valuation `v₂(L)` of the run length, not on `n` (= `2^m`):

> **`norm_run_eq` :  `N_{K/ℚ}(∑_{i<L} ζ^i) = 2^{2^{v₂(L)} - 1}`**   (for `2 ≤ m`, `1 ≤ L < 2^m`).

Numerically (matching the probe `scripts/probes/probe_407_halfsum_run`, all `1 ≤ L < n`):
`v₂(L)=0 → 2^0`, `v₂(L)=1 → 2^1`, `v₂(L)=2 → 2^3`, `v₂(L)=3 → 2^7`, `v₂(L)=4 → 2^15`, …
The exponent `2^{v₂(L)} - 1` is **the same for every `n`** — the closed form is genuinely
uniform across the whole 2-power tower, not a per-`n` value.

Specializing `L = n/2 = 2^{m-1}` (so `v₂(L) = m-1`) recovers
`2^{2^{m-1} - 1} = 2^{n/2 - 1}`, exactly `HalfSumNormClosedForm.norm_halfSum_eq`
(`run_norm_eq_halfSum`).

## Mechanism

The run telescopes: `(ζ - 1)·(∑_{i<L} ζ^i) = ζ^L - 1` (`mul_geom_sum`). Taking norms and
using `N(ζ - 1) = 2` (`IsPrimitiveRoot.norm_sub_one_two`), it reduces to the norm of `ζ^L - 1`.
Writing `L = 2^v · b` with `b` odd (`v = v₂(L)`, `b = ordCompl[2] L`), `b` is coprime to
`2^m`, so `ζ^b` is *also* a primitive `2^m`-th root of unity, and
`ζ^L = (ζ^b)^{2^v}`. Mathlib's `IsPrimitiveRoot.norm_pow_sub_one_eq_prime_pow_of_ne_zero`
then gives `N((ζ^b)^{2^v} - 1) = 2^{2^v}`, hence `N(∑_{i<L} ζ^i) = 2^{2^v}/2 = 2^{2^v - 1}`.

## Why this matters for the prize

Each consecutive run subset sum `U = {ζ^a, …, ζ^{a+L-1}}` (any start `a`, any length `L`)
has norm a **pure power of `2`**, *uniformly in `n`*, so it is divisible by **no odd prime**
— hence contributes **no** odd-prime bad-prime candidate `p ≡ 1 mod n` to the ledger, at every
level `n` simultaneously. This removes the entire family of run-shaped (and rotation-of-run)
subset sums from the candidate-norm enumeration uniformly, generalizing the single all-ones
half-sum from `HalfSumNormClosedForm.lean` to the full run family.

It does **not** resolve the full Half-Sum Lemma: general *non-run* antipodal-free subsets `U`
can have norms with genuine odd-prime factors `p ≡ 1 mod n` (the open candidates — e.g. the
weight-3 antipodal-free sums of `μ₁₆` realize `p = 17`, those of `μ₃₂` realize `p = 97`;
see `DISPROOF_LOG.md`). The open residual is the structure of those non-run subsets, which is
the BGK / Lam–Leung char-`p` wall. This file is a pure cyclotomic-arithmetic identity, uniform
in `n`, with no analytic input.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.HalfSumRunNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `(2 : K) ≠ 0` in a 2-power cyclotomic extension (`m ≥ 1`): the conductor `2^m` is
invertible, so `2` is. -/
theorem two_ne_zero_of_cyclotomic {m : ℕ} (hm : 1 ≤ m) [NeZero ((2 : ℕ) ^ m)]
    [IsCyclotomicExtension {(2 : ℕ) ^ m} K L] : (2 : K) ≠ 0 := by
  haveI hnz : NeZero (((2 : ℕ) ^ m : ℕ) : K) :=
    IsCyclotomicExtension.neZero' ((2 : ℕ) ^ m) K L
  have h0 : (((2 : ℕ) ^ m : ℕ) : K) ≠ 0 := hnz.ne
  rw [Nat.cast_pow, Nat.cast_ofNat] at h0
  exact fun h2 => h0 (by rw [h2, zero_pow (by omega)])

/-- **The run telescoping identity.** Over any `ζ`, `(ζ - 1)·(∑_{i<L} ζ^i) = ζ^L - 1`
(the geometric series). -/
theorem run_mul_sub_one {ζ : L} (Lrun : ℕ) :
    (ζ - 1) * (∑ i ∈ range Lrun, ζ ^ i) = ζ ^ Lrun - 1 := mul_geom_sum ζ Lrun

/-- **The norm of `ζ^L - 1` is `2^{2^{v₂(L)}}`, uniformly in `m`.**
For a primitive `2^m`-th root of unity `ζ` (`m ≥ 2`) and `1 ≤ L < 2^m`, writing
`v = v₂(L) = L.factorization 2` (so `v ≤ m-1`),

`N_{K/ℚ}(ζ^L - 1) = 2^{2^v}`.

The key step is `ζ^L = (ζ^b)^{2^v}` with `b = ordCompl[2] L` odd (hence coprime to `2^m`),
so `ζ^b` is again a primitive `2^m`-th root of unity, and Mathlib's
`norm_pow_sub_one_eq_prime_pow_of_ne_zero` computes the prime-power norm of `(ζ^b)^{2^v} - 1`. -/
theorem norm_zeta_pow_sub_one {m : ℕ} (hm : 2 ≤ m) {ζ : L}
    {Lrun : ℕ} (hL1 : 1 ≤ Lrun) (hL2 : Lrun < 2 ^ m)
    [NeZero ((2 : ℕ) ^ m)]
    (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ m))
    [IsCyclotomicExtension {(2 : ℕ) ^ m} K L]
    (hirr : Irreducible (cyclotomic ((2 : ℕ) ^ m) K)) :
    Algebra.norm K (ζ ^ Lrun - 1) = (2 : K) ^ (2 ^ (Lrun.factorization 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := Lrun.factorization 2 with hv
  set b := ordCompl[2] Lrun with hb
  have hLne : Lrun ≠ 0 := by omega
  -- L = 2^v * b  (ordProj * ordCompl = self)
  have hdecomp : Lrun = 2 ^ v * b := by
    rw [hv, hb]; exact (Nat.ordProj_mul_ordCompl_eq_self Lrun 2).symm
  -- b is odd, hence coprime to 2^m
  have hbcop : Nat.Coprime b 2 := (Nat.coprime_ordCompl Nat.prime_two hLne).symm
  have hbcopm : Nat.Coprime b (2 ^ m) := hbcop.pow_right m
  -- ζ^b is again a primitive 2^m-th root of unity
  have hζb : IsPrimitiveRoot (ζ ^ b) (2 ^ m) := hζ.pow_of_coprime b hbcopm
  -- v ≤ m - 1, from 2^v ∣ L ≤ L < 2^m
  have hvm : v ≤ m - 1 := by
    have h2v : 2 ^ v ∣ Lrun := by rw [hv]; exact Nat.ordProj_dvd Lrun 2
    have h2vle : 2 ^ v ≤ Lrun := Nat.le_of_dvd (by omega) h2v
    have hlt : (2 : ℕ) ^ v < 2 ^ m := lt_of_le_of_lt h2vle hL2
    have : v < m := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    omega
  -- ζ^L = (ζ^b)^{2^v}
  have hrw : ζ ^ Lrun = (ζ ^ b) ^ (2 ^ v) := by
    rw [← pow_mul]; congr 1; rw [hdecomp]; ring
  rw [hrw]
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  have hkne : k ≠ 0 := by omega
  have hsk : v ≤ k := by omega
  have hζb' : IsPrimitiveRoot (ζ ^ b) ((2 : ℕ) ^ (k + 1)) := hζb
  have := hζb'.norm_pow_sub_one_eq_prime_pow_of_ne_zero (K := K) hirr hsk hkne
  simpa using this

/-- **The uniform-in-`n` run-sum norm closed form.** For a primitive `2^m`-th root of unity `ζ`
(`m ≥ 2`) and a run length `1 ≤ L < 2^m = n`,

`N_{K/ℚ}(1 + ζ + ⋯ + ζ^{L-1}) = 2^{2^{v₂(L)} - 1}`,

a pure power of `2` depending **only** on the `2`-adic valuation of `L` — uniformly in `n`.

Specializing `L = 2^{m-1} = n/2` (so `v₂(L) = m-1`) recovers the all-ones half-sum value
`2^{2^{m-1} - 1} = 2^{n/2 - 1}` (`HalfSumNormClosedForm.norm_halfSum_eq`; see
`run_norm_eq_halfSum`). For ANY run length the norm is a pure power of `2`, hence divisible by
NO odd prime, **uniformly across `n`** (see `odd_prime_not_dvd_run_norm`). -/
theorem norm_run_eq {m : ℕ} (hm : 2 ≤ m) {ζ : L}
    {Lrun : ℕ} (hL1 : 1 ≤ Lrun) (hL2 : Lrun < 2 ^ m)
    [NeZero ((2 : ℕ) ^ m)]
    (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ m))
    [IsCyclotomicExtension {(2 : ℕ) ^ m} K L]
    (hirr : Irreducible (cyclotomic ((2 : ℕ) ^ m) K)) :
    Algebra.norm K (∑ i ∈ range Lrun, ζ ^ i) = (2 : K) ^ (2 ^ (Lrun.factorization 2) - 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := Lrun.factorization 2 with hv
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hζ2k : IsPrimitiveRoot ζ ((2 : ℕ) ^ (k + 1)) := by rw [← hk]; exact hζ
  -- N(ζ - 1) = 2
  have hnormsub1 : Algebra.norm K (ζ - 1) = (2 : K) := by
    have hkge : 2 ≤ k + 1 := by omega
    haveI : IsCyclotomicExtension {(2 : ℕ) ^ (k+1)} K L := by rw [← hk]; infer_instance
    have hirr' : Irreducible (cyclotomic ((2 : ℕ) ^ (k+1)) K) := by rw [← hk]; exact hirr
    have := hζ2k.norm_sub_one_two (K := K) hkge hirr'
    simpa using this
  -- N(ζ - 1) · N(run) = N(ζ^L - 1) = 2^{2^v}
  have hmul : Algebra.norm K (ζ - 1) * Algebra.norm K (∑ i ∈ range Lrun, ζ ^ i)
      = (2 : K) ^ (2 ^ v) := by
    rw [← map_mul, run_mul_sub_one, norm_zeta_pow_sub_one hm hL1 hL2 hζ hirr]
  rw [hnormsub1] at hmul
  -- 2 · N(run) = 2^{2^v} = 2 · 2^{2^v - 1}, cancel
  have hvpos : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  have hpow : (2 : K) ^ (2 ^ v) = 2 * (2 : K) ^ (2 ^ v - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow] at hmul
  exact mul_left_cancel₀ (two_ne_zero_of_cyclotomic (m := m) (L := L) (by omega)) hmul

/-- **Specialization to the all-ones half-sum.** The run of length `L = 2^{m-1} = n/2` has
`v₂(L) = m-1`, so `norm_run_eq` gives the value `2^{2^{m-1} - 1} = 2^{n/2 - 1}` — exactly
`HalfSumNormClosedForm.norm_halfSum_eq`. This confirms the uniform run formula generalizes the
single all-ones half-sum. -/
theorem run_norm_eq_halfSum {m : ℕ} (hm : 2 ≤ m) {ζ : L}
    [NeZero ((2 : ℕ) ^ m)]
    (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ m))
    [IsCyclotomicExtension {(2 : ℕ) ^ m} K L]
    (hirr : Irreducible (cyclotomic ((2 : ℕ) ^ m) K)) :
    Algebra.norm K (∑ i ∈ range (2 ^ (m - 1)), ζ ^ i) = (2 : K) ^ (2 ^ (m - 1) - 1) := by
  have hL1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have hL2 : 2 ^ (m - 1) < 2 ^ m := by
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hfac : (2 ^ (m - 1)).factorization 2 = m - 1 :=
    Nat.factorization_pow_self Nat.prime_two
  rw [norm_run_eq hm hL1 hL2 hζ hirr, hfac]

/-- **The run-sum norm is a pure power of `2` (abstract, non-vacuous).** For every run length
`1 ≤ L < n = 2^m` (`m ≥ 2`), `N_{K/ℚ}(∑_{i<L} ζ^i)` is `2^e` for `e = 2^{v₂(L)} - 1`. This is
the abstract "pure power of 2" statement over any 2-power cyclotomic `K ⊆ L`. -/
theorem run_norm_isPowerOfTwo {m : ℕ} (hm : 2 ≤ m) {ζ : L}
    {Lrun : ℕ} (hL1 : 1 ≤ Lrun) (hL2 : Lrun < 2 ^ m)
    [NeZero ((2 : ℕ) ^ m)]
    (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ m))
    [IsCyclotomicExtension {(2 : ℕ) ^ m} K L]
    (hirr : Irreducible (cyclotomic ((2 : ℕ) ^ m) K)) :
    ∃ e : ℕ, Algebra.norm K (∑ i ∈ range Lrun, ζ ^ i) = (2 : K) ^ e :=
  ⟨2 ^ (Lrun.factorization 2) - 1, norm_run_eq hm hL1 hL2 hζ hirr⟩

/-- **The prize-relevant uniform consequence: no odd prime divides a run-sum norm.**
With base field `ℚ` and `L` a genuine `2^m`-th cyclotomic number field (the
`IsCyclotomicExtension {2^m} ℚ L` hypothesis is *satisfiable* — e.g. `L = CyclotomicField`,
see `cyclotomicField_inhabits_hypotheses` below for an explicit witness instance), for every run
length `1 ≤ L < n = 2^m` (`m ≥ 2`) and any primitive `2^m`-th root `ζ`, the norm
`N_{ℚ(ζ_n)/ℚ}(∑_{i<L} ζ^i)` is a pure power of `2`, so any odd `p > 1` — in particular any odd
prime `p ≡ 1 mod n` — does **not** divide its (integer) numerator. Uniformly in `n`. Hence the
entire consecutive-run family contributes no odd-prime bad-prime candidate, at every level. -/
theorem odd_prime_not_dvd_run_norm {m : ℕ} (hm : 2 ≤ m)
    {L : Type*} [Field L] [Algebra ℚ L]
    {ζ : L}
    {Lrun : ℕ} (hL1 : 1 ≤ Lrun) (hL2 : Lrun < 2 ^ m)
    [NeZero ((2 : ℕ) ^ m)]
    (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ m))
    [IsCyclotomicExtension {(2 : ℕ) ^ m} ℚ L]
    (hirr : Irreducible (cyclotomic ((2 : ℕ) ^ m) ℚ))
    {p : ℕ} (hp_odd : Odd p) (hp1 : 1 < p) :
    ¬ (p : ℤ) ∣ (Algebra.norm ℚ (∑ i ∈ range Lrun, ζ ^ i)).num := by
  classical
  -- the norm is 2^{2^v - 1} : ℚ, an integer; its numerator is 2^{2^v - 1} : ℤ
  have hnorm := norm_run_eq hm hL1 hL2 hζ hirr
  -- num of (2 : ℚ)^e is (2 : ℤ)^e
  have hnum : (Algebra.norm ℚ (∑ i ∈ range Lrun, ζ ^ i)).num
      = (2 : ℤ) ^ (2 ^ (Lrun.factorization 2) - 1) := by
    rw [hnorm]
    have : ((2 : ℚ) ^ (2 ^ (Lrun.factorization 2) - 1))
        = (((2 : ℤ) ^ (2 ^ (Lrun.factorization 2) - 1) : ℤ) : ℚ) := by push_cast; ring
    rw [this, Rat.num_intCast]
  rw [hnum]
  -- an odd p > 1 does not divide a power of 2
  intro hdvd
  have hcop : IsCoprime (p : ℤ) 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hco : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hp_odd
    simpa [Int.gcd] using hco
  have hcoppow : IsCoprime (p : ℤ) (2 ^ (2 ^ (Lrun.factorization 2) - 1)) :=
    hcop.pow_right
  have hone : (p : ℤ) ∣ 1 := hcoppow.dvd_of_dvd_mul_right (by simpa using hdvd.mul_right 1)
  have hple : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hone
  exact absurd hple (by exact_mod_cast (by omega : ¬ p ≤ 1))

/-- **Non-vacuity witness.** The hypothesis bundle of `odd_prime_not_dvd_run_norm` is genuinely
inhabited at every level: `L = CyclotomicField (2^(k+2)) ℚ` carries the
`IsCyclotomicExtension {2^(k+2)} ℚ L` instance, so the abstract theorem applies to a real
`2^m`-th cyclotomic number field — it is not vacuously true. -/
theorem cyclotomicField_inhabits_hypotheses (k : ℕ) :
    IsCyclotomicExtension {(2 : ℕ) ^ (k + 2)} ℚ (CyclotomicField ((2 : ℕ) ^ (k + 2)) ℚ) := by
  haveI : NeZero ((2 : ℕ) ^ (k + 2)) := ⟨by positivity⟩
  haveI : NeZero (((2 : ℕ) ^ (k + 2) : ℕ) : ℚ) := by
    refine ⟨?_⟩
    have h : ((2 : ℕ) ^ (k + 2) : ℚ) ≠ 0 := by positivity
    simp only [Nat.cast_pow, Nat.cast_ofNat]; exact h
  exact CyclotomicField.isCyclotomicExtension _ _

end ArkLib.ProximityGap.HalfSumRunNorm

#print axioms ArkLib.ProximityGap.HalfSumRunNorm.norm_zeta_pow_sub_one
#print axioms ArkLib.ProximityGap.HalfSumRunNorm.norm_run_eq
#print axioms ArkLib.ProximityGap.HalfSumRunNorm.run_norm_eq_halfSum
#print axioms ArkLib.ProximityGap.HalfSumRunNorm.run_norm_isPowerOfTwo
#print axioms ArkLib.ProximityGap.HalfSumRunNorm.odd_prime_not_dvd_run_norm
#print axioms ArkLib.ProximityGap.HalfSumRunNorm.cyclotomicField_inhabits_hypotheses
