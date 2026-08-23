/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

/-!
# The half-sum cyclotomic norm closed form (#407 — Half-Sum Lemma, GRIND T5)

The Half-Sum Lemma (issue #407, the irreducible non-BGK residual of the Proximity Prize)
asks for the structure of antipodal-free vanishing sums of `2^μ`-th roots of unity in the
split regime `p ≡ 1 mod 2^μ`. The candidate-bad-prime method reduces the per-`n` statement
to the algebraic norm `N_{ℚ(ζ_n)/ℚ}(∑_{u ∈ U} u)` of subset sums `U ⊆ μ_n`: a bad prime
must divide one of these norms.

The **base point of that ledger** — the "all-ones" half-sum
`α = 1 + ζ + ⋯ + ζ^{n/2-1}` over a primitive `n = 2^{m+1}`-th root of unity — has an exact
closed form. This file proves it,
char-`0`, axiom-clean, uniformly in `m`:

> **`norm_halfSum_eq` :  `N_{K/ℚ}(∑_{i < 2^m} ζ^i) = 2^{2^m - 1}`**

(for any cyclotomic extension `K ⊆ L` of conductor `2^{m+1}`, `m ≥ 1`). Numerically:
`n = 8 → 2³ = 8`, `n = 16 → 2⁷ = 128`, `n = 32 → 2¹⁵ = 32768`, `n = 64 → 2³¹` —
matching the probe `scripts/probes/probe_407_halfsum_*` exactly.

## Mechanism (the proof is short and structural)

Since `ζ^{2^m} = -1` (the defining negation of the prime-2 tower, `LamLeungTwoPow`), the
geometric series telescopes:
`(ζ - 1)·(∑_{i < 2^m} ζ^i) = ζ^{2^m} - 1 = -2`.
Taking the multiplicative `K`-norm and using two Mathlib facts —
`N(ζ - 1) = (2^{m+1}).minFac = 2` (`IsPrimitiveRoot.sub_one_norm_isPrimePow`) and
`N(-2) = (-2)^{φ(2^{m+1})} = (-2)^{2^m} = 2^{2^m}` (`Algebra.norm_algebraMap` +
`IsCyclotomicExtension.finrank`) — gives `2·N(α) = 2^{2^m}`, hence `N(α) = 2^{2^m - 1}`.

## Why this matters for the prize

This is the **clean, uniform-in-n sub-result** the GRIND T5 thread asks for: the all-ones
half-sum has norm a pure power of `2`, so it can **never** be divisible by an odd prime
`p ≡ 1 mod n` — the base case of "no antipodal-free subset of the full half-coset structure
contributes a bad prime". It pins the simplest member of the candidate-norm ledger
unconditionally and uniformly, removing it from the finite enumeration at every level `n`. It
does NOT resolve the full Half-Sum Lemma (general antipodal-free `U` can have norms with
genuine odd-prime factors — e.g. `N = 9` at `n = 8`, `N = 17, 97, …` at `n = 16`; those primes
`≡ 1 mod n` are the open candidates), and it does not touch the BGK character-sum wall: it is
a pure cyclotomic-arithmetic identity.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.HalfSumNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- In a cyclotomic extension of conductor `2^{m+1}`, the base field has `(2 : K) ≠ 0`
(the conductor `2^{m+1}` is invertible, so `2` is). -/
theorem two_ne_zero_of_cyclotomic {m : ℕ} [NeZero ((2:ℕ) ^ (m + 1))]
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L] : (2 : K) ≠ 0 := by
  haveI hnz : NeZero (((2:ℕ) ^ (m + 1) : ℕ) : K) :=
    IsCyclotomicExtension.neZero' ((2:ℕ) ^ (m + 1)) K L
  have h0 : (((2:ℕ) ^ (m + 1) : ℕ) : K) ≠ 0 := hnz.ne
  rw [Nat.cast_pow, Nat.cast_ofNat] at h0
  exact fun h2 => h0 (by rw [h2]; ring)

/-- A primitive `2^{m+1}`-th root of unity has `ζ^{2^m} = -1` (the prime-2 negation). -/
theorem pow_half_eq_neg_one {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    ζ ^ (2 ^ m) = -1 := by
  have hsq : (ζ ^ 2 ^ m) ^ 2 = 1 := by
    rw [← pow_mul, show 2 ^ m * 2 = 2 ^ (m + 1) by ring]; exact hζ.pow_eq_one
  have hne : ζ ^ 2 ^ m ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos m).ne'
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hfac : (ζ ^ 2 ^ m - 1) * (ζ ^ 2 ^ m + 1) = 0 := by ring_nf; linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- **The telescoping identity.** Over a primitive `2^{m+1}`-th root, the all-ones half-sum
`∑_{i < 2^m} ζ^i` times `(ζ - 1)` collapses to `-2`. -/
theorem halfSum_mul_sub_one {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    (ζ - 1) * (∑ i ∈ range (2 ^ m), ζ ^ i) = -2 := by
  rw [mul_geom_sum, pow_half_eq_neg_one hζ]; ring

/-- `N_{K/ℚ}(ζ - 1) = 2` for `ζ` a primitive `2^{m+1}`-th root (`m ≥ 1`). The `minFac` of a
2-power prime power is `2`. -/
theorem norm_sub_one {m : ℕ} (hm : 1 ≤ m) {ζ : L} [NeZero ((2:ℕ) ^ (m + 1))]
    (hζ : IsPrimitiveRoot ζ ((2:ℕ) ^ (m + 1)))
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (ζ - 1) = (2 : K) := by
  have hpp : IsPrimePow ((2:ℕ) ^ (m + 1)) := ⟨2, m + 1, Nat.prime_two.prime, by omega, rfl⟩
  have hne2 : (2 : ℕ) ^ (m + 1) ≠ 2 := by
    have : (2:ℕ) ^ (m + 1) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmf : Nat.minFac ((2:ℕ) ^ (m + 1)) = 2 := by
    rw [Nat.minFac_eq, if_pos (dvd_pow_self 2 (Nat.succ_ne_zero m))]
  rw [hζ.sub_one_norm_isPrimePow hpp hirr hne2, hmf]; norm_num

/-- `N_{K/ℚ}(-2) = (-2)^{φ(2^{m+1})} = (-2)^{2^m} = 2^{2^m}` (`2^m` is even for `m ≥ 1`). -/
theorem norm_neg_two {m : ℕ} (hm : 1 ≤ m) [NeZero ((2:ℕ) ^ (m + 1))]
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (-2 : L) = (2 : K) ^ (2 ^ m) := by
  have h1 : (-2 : L) = algebraMap K L (-2 : K) := by rw [map_neg, map_ofNat]
  rw [h1, Algebra.norm_algebraMap, IsCyclotomicExtension.finrank L hirr,
      Nat.totient_prime_pow_succ Nat.prime_two]
  -- exponent simplifies: 2^m * (2-1) = 2^m
  have hexp : 2 ^ m * (2 - 1) = 2 ^ m := by omega
  rw [hexp]
  -- (-2)^(2^m) = 2^(2^m) since 2^m is even
  have heven : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  rw [neg_pow, heven.neg_one_pow, one_mul]

/-- **The half-sum norm closed form.** For a cyclotomic extension of conductor `n = 2^{m+1}`
(`m ≥ 1`) and `ζ` a primitive `n`-th root of unity,
`N_{K/ℚ}(1 + ζ + ⋯ + ζ^{n/2 - 1}) = 2^{n/2 - 1}`.

Verified numerically: `n = 8 → 8`, `n = 16 → 128`, `n = 32 → 32768`, `n = 64 → 2^31`. -/
theorem norm_halfSum_eq {m : ℕ} (hm : 1 ≤ m) {ζ : L} [NeZero ((2:ℕ) ^ (m + 1))]
    (hζ : IsPrimitiveRoot ζ ((2:ℕ) ^ (m + 1)))
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (∑ i ∈ range (2 ^ m), ζ ^ i) = (2 : K) ^ (2 ^ m - 1) := by
  -- N(ζ - 1) * N(α) = N((ζ-1)*α) = N(-2) = 2^(2^m)
  have hmul : Algebra.norm K (ζ - 1) * Algebra.norm K (∑ i ∈ range (2 ^ m), ζ ^ i)
      = (2 : K) ^ (2 ^ m) := by
    rw [← map_mul, halfSum_mul_sub_one hζ, norm_neg_two hm hirr]
  rw [norm_sub_one hm hζ hirr] at hmul
  -- 2 * N(α) = 2^(2^m) = 2 * 2^(2^m - 1)
  have hpow : (2 : K) ^ (2 ^ m) = 2 * (2 : K) ^ (2 ^ m - 1) := by
    rw [← pow_succ']
    congr 1
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  rw [hpow] at hmul
  exact mul_left_cancel₀ (two_ne_zero_of_cyclotomic (m := m) (L := L)) hmul


/-- **Rotated half-sums share the closed form.** For any exponent `a`, the rotation
`ζ^a · (1 + ζ + ⋯ + ζ^{n/2-1})` of the all-ones half-sum has the same norm `2^{n/2-1}`,
because `ζ` is a unit with `N_{K/ℚ}(ζ) = 1` (`IsPrimitiveRoot.norm_eq_one`, `n = 2^{m+1} ≠ 2`).
Hence the **entire `⟨ζ⟩`-rotation orbit** of the half-run subset sum has norm a pure power of
`2` and contributes **no** odd-prime bad-prime candidate — extending the Half-Sum base ledger
from the single all-ones run to its whole `n/2`-element rotation orbit, uniformly in `m`. -/
theorem norm_rotated_halfSum_eq {m : ℕ} (hm : 1 ≤ m) {ζ : L} (a : ℕ)
    [NeZero ((2:ℕ) ^ (m + 1))]
    (hζ : IsPrimitiveRoot ζ ((2:ℕ) ^ (m + 1)))
    [IsCyclotomicExtension {(2:ℕ) ^ (m + 1)} K L]
    (hirr : Irreducible (cyclotomic ((2:ℕ) ^ (m + 1)) K)) :
    Algebra.norm K (ζ ^ a * ∑ i ∈ range (2 ^ m), ζ ^ i) = (2 : K) ^ (2 ^ m - 1) := by
  have hn : ((2:ℕ) ^ (m + 1)) ≠ 2 := by
    have : (2:ℕ) ^ (m + 1) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [map_mul, map_pow, hζ.norm_eq_one hn hirr, one_pow, one_mul, norm_halfSum_eq hm hζ hirr]


/-- **Antipodal pairs cancel** — the atom of the antipodal-free reduction. Since `ζ^{2^m} = −1`
(`pow_half_eq_neg_one`, the prime-2 negation), `ζ^{a + 2^m} = −ζ^a`, so `ζ^a + ζ^{a + 2^m} = 0`.
Hence any `U ⊆ μ_n` closed under the antipodal involution `x ↦ −x = ζ^{2^m}·x` sums to `0`, and
**only antipodal-free `U` contribute a candidate bad-prime norm** — the structural reduction the
Half-Sum Lemma rests on. -/
theorem antipodal_pair_sum_zero {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) (a : ℕ) :
    ζ ^ a + ζ ^ (a + 2 ^ m) = 0 := by
  rw [pow_add, pow_half_eq_neg_one hζ, mul_neg_one, add_neg_cancel]


/-- **Antipodal pairs cancel over a half-run** — the run-level lift of `antipodal_pair_sum_zero`.
Summing the `2^m` antipodal pairs `ζ^{a+i} + ζ^{(a+i)+2^m}` over `i ∈ range (2^m)` gives `0`,
since each summand is an antipodal pair and vanishes by `antipodal_pair_sum_zero hζ (a + i)`. -/
theorem antipodal_run_sum_zero {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) (a : ℕ) :
    (∑ i ∈ Finset.range (2 ^ m), (ζ ^ (a + i) + ζ ^ (a + i + 2 ^ m))) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h := antipodal_pair_sum_zero hζ (a + i)
  -- `h : ζ ^ (a + i) + ζ ^ ((a + i) + 2 ^ m) = 0`; goal exponent `a + i + 2^m = (a+i) + 2^m`.
  simpa using h

/-- **Antipodal-closed sets vanish** — the structural form. For a set `A ⊆ range (2^(m+1))` of
canonical residues closed under the antipodal involution `a ↦ (a + 2^m) % 2^(m+1)`, the sum
`∑_{a ∈ A} ζ^a = 0`. Each antipodal pair `{a, g a}` contributes `ζ^a + ζ^{g a} = 0` by
`antipodal_pair_sum_zero`, and `g` is a fixed-point-free involution on `range (2^(m+1))`. -/
theorem antipodal_symmetric_sum_zero {m : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) (A : Finset ℕ)
    (hAsub : A ⊆ Finset.range (2 ^ (m + 1)))
    (hA : ∀ a ∈ A, (a + 2 ^ m) % 2 ^ (m + 1) ∈ A) :
    (∑ a ∈ A, ζ ^ a) = 0 := by
  -- `g a = (a + 2^m) % 2^(m+1)`.  `ζ^{g a} = ζ^{a + 2^m}` for all `a` (order `2^(m+1)`).
  -- Generic fact: `ζ ^ (k % 2^(m+1)) = ζ ^ k` since `ζ ^ 2^(m+1) = 1`.
  have hpowmod : ∀ k : ℕ, ζ ^ (k % 2 ^ (m + 1)) = ζ ^ k := by
    intro k
    set n := 2 ^ (m + 1) with hn
    conv_rhs => rw [← Nat.mod_add_div k n]
    rw [pow_add]
    have hone : ζ ^ (n * (k / n)) = 1 := by
      rw [pow_mul]
      rw [show ζ ^ n = 1 from by rw [hn]; exact hζ.pow_eq_one]
      rw [one_pow]
    rw [hone, mul_one]
  have hmod : ∀ a : ℕ, ζ ^ ((a + 2 ^ m) % 2 ^ (m + 1)) = ζ ^ (a + 2 ^ m) := fun a => hpowmod _
  -- `2^m < 2^(m+1)`, and `2^m ≠ 0`.
  have hlt : (2 : ℕ) ^ m < 2 ^ (m + 1) := by
    have h2 : (1 : ℕ) < 2 := one_lt_two
    have := Nat.pow_lt_pow_right h2 (Nat.lt_succ_self m)
    simpa using this
  have hpos : 0 < (2 : ℕ) ^ (m + 1) := by positivity
  refine Finset.sum_involution (fun a _ => (a + 2 ^ m) % 2 ^ (m + 1)) ?_ ?_ ?_ ?_
  · -- pairing cancels: `ζ^a + ζ^{g a} = 0`.
    intro a ha
    rw [hmod a]
    exact antipodal_pair_sum_zero hζ a
  · -- `g a ≠ a` for `a ∈ A` (since `a < 2^(m+1)` and adding `2^m` mod changes the residue).
    intro a ha _ hcontra
    simp only [] at hcontra
    -- `hcontra : (a + 2^m) % 2^(m+1) = a`.  `a < 2^(m+1)`, so `a % 2^(m+1) = a`.
    have halt : a < 2 ^ (m + 1) := Finset.mem_range.mp (hAsub ha)
    have ha' : a % 2 ^ (m + 1) = a := Nat.mod_eq_of_lt halt
    -- congruence: `(a + 2^m) ≡ a [MOD 2^(m+1)]` ⟹ `2^m ≡ 0 [MOD 2^(m+1)]`, impossible.
    have hcong : (a + 2 ^ m) ≡ a [MOD 2 ^ (m + 1)] := by
      unfold Nat.ModEq; rw [hcontra, ha']
    have hcong0 : (a + 2 ^ m) ≡ (a + 0) [MOD 2 ^ (m + 1)] := by simpa using hcong
    have hz : (2 : ℕ) ^ m ≡ 0 [MOD 2 ^ (m + 1)] := (Nat.ModEq.add_left_cancel' a hcong0)
    have : (2 : ℕ) ^ m % 2 ^ (m + 1) = 0 := by simpa [Nat.ModEq, Nat.zero_mod] using hz
    rw [Nat.mod_eq_of_lt hlt] at this
    exact (pow_ne_zero m (by norm_num : (2 : ℕ) ≠ 0)) this
  · -- membership: `g` maps `A` into `A`.
    intro a ha
    exact hA a ha
  · -- involutivity: `g (g a) = a` for `a ∈ A` (uses `a < 2^(m+1)`).
    intro a ha
    simp only []
    have halt : a < 2 ^ (m + 1) := Finset.mem_range.mp (hAsub ha)
    -- `g (g a) ≡ (a + 2^m) + 2^m = a + 2^(m+1) ≡ a [MOD 2^(m+1)]`, and `g(g a) < 2^(m+1)`.
    set n := 2 ^ (m + 1) with hn
    -- congruence `(a + 2^m) % n + 2^m ≡ a [MOD n]`.
    have e1 : ((a + 2 ^ m) % n + 2 ^ m) ≡ ((a + 2 ^ m) + 2 ^ m) [MOD n] :=
      (Nat.mod_modEq (a + 2 ^ m) n).add_right (2 ^ m)
    have e2 : (a + 2 ^ m) + 2 ^ m = a + n := by
      rw [hn, pow_succ]; ring
    have e3 : ((a + 2 ^ m) % n + 2 ^ m) ≡ a [MOD n] := by
      calc ((a + 2 ^ m) % n + 2 ^ m) ≡ ((a + 2 ^ m) + 2 ^ m) [MOD n] := e1
        _ = a + n := e2
        _ ≡ a + 0 [MOD n] := (Nat.modEq_zero_iff_dvd.mpr (dvd_refl n)).add_left a
        _ = a := by rw [add_zero]
    -- both sides `< n`, so the `[MOD n]` equality is an equality.
    have hlhs : ((a + 2 ^ m) % n + 2 ^ m) % n < n := Nat.mod_lt _ (by rw [hn]; positivity)
    have := e3
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt halt] at this
    exact this


/-- **The full-group sum of all `n`-th roots vanishes** (`n = 2^{m+1}`).

The base-ledger member: the full geometric sum `∑_{i < 2^{m+1}} ζ^i` over a primitive
`2^{m+1}`-th root of unity collapses to `0`. Indeed `(ζ - 1) · ∑ = ζ^{2^{m+1}} - 1 = 0` by
the telescoping geometric identity (`mul_geom_sum`) and `ζ^{2^{m+1}} = 1`
(`hζ.pow_eq_one`); cancel the nonzero factor `ζ - 1` (since `ζ ≠ 1`, as `1 < 2^{m+1}`).

Hence the **full-group subset sum is trivially non-bad** — it contributes no odd-prime
candidate to the Half-Sum bad-prime ledger. -/
theorem full_group_sum_eq_zero {m : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    (∑ i ∈ Finset.range (2 ^ (m + 1)), ζ ^ i) = 0 := by
  have h1lt : 1 < 2 ^ (m + 1) := by
    have : (2:ℕ) ^ (m + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one h1lt)
  have hfac : (ζ - 1) * (∑ i ∈ Finset.range (2 ^ (m + 1)), ζ ^ i) = 0 := by
    rw [mul_geom_sum, hζ.pow_eq_one]; ring
  exact (mul_eq_zero.mp hfac).resolve_left hne


/-- **Galois/rotation symmetry of the half-sum norm.** For `k` odd, `ζ^k` is again a
primitive `2^{m+1}`-th root of unity (since `gcd(k, 2^{m+1}) = 1` because `2^{m+1}` is a
power of 2 and `k` is odd), so the power-rotated half-sum `∑_{i<2^m} (ζ^k)^i` has the **same**
closed-form norm `2^{2^m-1}` as the all-ones half-sum. This extends the Half-Sum base ledger
across the whole Galois `(ℤ/2^{m+1})^×`-orbit of generators: every odd power `ζ^k` of a fixed
primitive root yields the identical pure-power-of-2 norm, hence contributes **no** odd-prime
bad-prime candidate, uniformly in `m`. -/
theorem norm_halfSum_pow_eq {m : ℕ} (hm : 1 ≤ m) {ζ : L} (k : ℕ) (hk : Odd k)
    [NeZero ((2:ℕ)^(m+1))] (hζ : IsPrimitiveRoot ζ ((2:ℕ)^(m+1)))
    [IsCyclotomicExtension {(2:ℕ)^(m+1)} K L] (hirr : Irreducible (cyclotomic ((2:ℕ)^(m+1)) K)) :
    Algebra.norm K (∑ i ∈ range (2 ^ m), (ζ ^ k) ^ i) = (2 : K) ^ (2 ^ m - 1) := by
  have hcop : Nat.Coprime k ((2:ℕ)^(m+1)) := by
    rw [Nat.coprime_pow_right_iff (by omega)]
    have h2 : ¬ (2 ∣ k) := by
      rw [Nat.two_dvd_ne_zero]; exact Nat.odd_iff.mp hk
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr h2).symm
  have hζk : IsPrimitiveRoot (ζ ^ k) ((2:ℕ)^(m+1)) := hζ.pow_of_coprime k hcop
  exact norm_halfSum_eq hm hζk hirr


/-- **A root of unity is an algebraic integer.** If `ζ ^ n = 1` (with `0 < n`), then `ζ` is a
root of the monic integer polynomial `X ^ n - 1`, hence integral over `ℤ`. -/
theorem rootOfUnity_isIntegral {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : ζ ^ n = 1) :
    IsIntegral ℤ ζ := by
  refine ⟨X ^ n - 1, ?_, ?_⟩
  · exact monic_X_pow_sub (by simp [Polynomial.degree_one]; exact_mod_cast hn)
  · -- eval₂ (algebraMap ℤ L) ζ (X^n - 1) = ζ^n - 1 = 0
    have : (Polynomial.aeval ζ) ((X : ℤ[X]) ^ n - 1) = 0 := by
      simp [map_sub, aeval_X_pow, hζ]
    simpa [Polynomial.aeval_def] using this

/-- **Any ℤ-sum of `n`-th roots of unity is an algebraic integer.** For `ζ ^ n = 1` (`0 < n`)
and any finite index set `S`, the subset sum `∑ a ∈ S, ζ ^ a` is integral over `ℤ`.

This is the foundation of the candidate-bad-prime method of the Half-Sum ledger (#407): each
`ζ ^ a` is a root of the monic integer polynomial `X ^ n - 1` (since `(ζ ^ a) ^ n = (ζ ^ n) ^ a
= 1`), hence `IsIntegral ℤ (ζ ^ a)`; integrality is closed under finite sums. Consequently the
algebraic norm `N_{K/ℚ}(∑ u)` of a subset sum lies in `ℤ`, so a bad prime can divide it. -/
theorem rootPow_sum_isIntegral {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : ζ ^ n = 1)
    (S : Finset ℕ) : IsIntegral ℤ (∑ a ∈ S, ζ ^ a) := by
  refine IsIntegral.sum (fun a => ζ ^ a) (fun a _ => ?_)
  -- each ζ^a is itself an n-th root of unity: (ζ^a)^n = (ζ^n)^a = 1
  have hpow : (ζ ^ a) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  exact rootOfUnity_isIntegral hn hpow


/-- **The norm of a ℤ-sum of roots of unity is an algebraic integer.** Completing the
candidate-bad-prime foundation of the Half-Sum ledger (#407): the algebraic norm
`N_{K/L'}(∑_{a∈S} ζ^a)` of any subset sum of powers of an `n`-th root of unity `ζ` is integral
over `ℤ`. Indeed, `∑_{a∈S} ζ^a` is integral over `ℤ` (`rootPow_sum_isIntegral`), and the
algebraic norm of an integral element is integral, being a product of Galois conjugates each
integral over `ℤ`. Specialized to `K = ℚ` this places the norm in `ℤ`, so a bad prime can
divide it. -/
theorem norm_rootPow_sum_isIntegral [IsScalarTower ℤ K L]
    {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : ζ ^ n = 1) (S : Finset ℕ) :
    IsIntegral ℤ (Algebra.norm K (∑ a ∈ S, ζ ^ a)) :=
  Algebra.isIntegral_norm K (rootPow_sum_isIntegral hn hζ S)


/-- **Antipodal-free sets are at most half the group.**
An antipodal-free subset `A` of the residues `range (2^(m+1))` — one that never contains both
`a` and its antipode `g a = (a + 2^m) % 2^(m+1)` — has at most `2^m` elements, i.e. at most half
of the `2^(m+1)` residues.

The fixed-point-free involution `g` pairs the `2^(m+1)` residues into `2^m` antipodal pairs;
an antipodal-free set picks at most one element from each pair. We realize the quotient by `g`
as the map `a ↦ a % 2^m`, which is constant on antipodal pairs and (because `A` is
antipodal-free) injective on `A`, into `range (2^m)`. Hence `card A ≤ card (range (2^m)) = 2^m`.

This is the base-case combinatorics of the Half-Sum ledger (#407, non-BGK, thread T5): the
candidate antipodal-free bad sets are at most half the group. Pure `ℕ`/`Finset`, no field. -/
theorem antipodal_free_card_le {m : ℕ} (A : Finset ℕ)
    (hAsub : A ⊆ Finset.range (2 ^ (m + 1)))
    (hfree : ∀ a ∈ A, (a + 2 ^ m) % 2 ^ (m + 1) ∉ A) :
    A.card ≤ 2 ^ m := by
  have hpow : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
  -- For `2^m ≤ x < 2^(m+1)`, `x % 2^m = x - 2^m`.
  have hmodsub : ∀ x : ℕ, 2 ^ m ≤ x → x < 2 ^ (m + 1) → x % 2 ^ m = x - 2 ^ m := by
    intro x hxlo hxhi
    rw [Nat.mod_eq_sub_mod hxlo, Nat.mod_eq_of_lt]
    rw [hpow] at hxhi; omega
  -- The map `a ↦ a % 2^m` is injective on `A`.
  have hInj : Set.InjOn (fun a => a % 2 ^ m) (A : Set ℕ) := by
    intro a ha a' ha' heq
    simp only at heq
    -- `a, a' < 2^(m+1)`
    have haR : a < 2 ^ (m + 1) := Finset.mem_range.mp (hAsub ha)
    have ha'R : a' < 2 ^ (m + 1) := Finset.mem_range.mp (hAsub ha')
    -- Suppose `a ≠ a'`; derive a contradiction with antipodal-freeness.
    by_contra hne
    -- WLOG analysis via the relation between `a` and `a'` modulo `2^m`.
    -- Since `a % 2^m = a' % 2^m` and both are `< 2^(m+1)`, the pair `{a, a'}` is `{x, x+2^m}`.
    -- Show `a' = (a + 2^m) % 2^(m+1)`, contradicting `hfree a ha`.
    -- a < 2^m or a ≥ 2^m
    rcases lt_or_ge a (2 ^ m) with haL | haH
    · -- a < 2^m so a % 2^m = a
      have hae : a % 2 ^ m = a := Nat.mod_eq_of_lt haL
      -- then a' % 2^m = a; and a' < 2^(m+1)
      rcases lt_or_ge a' (2 ^ m) with ha'L | ha'H
      · have ha'e : a' % 2 ^ m = a' := Nat.mod_eq_of_lt ha'L
        rw [hae, ha'e] at heq
        exact hne heq
      · -- a' ≥ 2^m, a' < 2^(m+1) ⇒ a' % 2^m = a' - 2^m
        have ha'e : a' % 2 ^ m = a' - 2 ^ m := hmodsub a' ha'H ha'R
        rw [hae, ha'e] at heq
        -- a = a' - 2^m, so a' = a + 2^m, and (a + 2^m) % 2^(m+1) = a + 2^m (since a+2^m < 2^(m+1))
        have hval : (a + 2 ^ m) % 2 ^ (m + 1) = a + 2 ^ m := by
          apply Nat.mod_eq_of_lt; rw [hpow]; omega
        have heq2 : (a + 2 ^ m) % 2 ^ (m + 1) = a' := by rw [hval]; omega
        exact hfree a ha (heq2 ▸ ha')
    · -- a ≥ 2^m, a < 2^(m+1) ⇒ a % 2^m = a - 2^m
      have hae : a % 2 ^ m = a - 2 ^ m := hmodsub a haH haR
      rcases lt_or_ge a' (2 ^ m) with ha'L | ha'H
      · have ha'e : a' % 2 ^ m = a' := Nat.mod_eq_of_lt ha'L
        rw [hae, ha'e] at heq
        -- a - 2^m = a', so a = a' + 2^m, antipode of a' is a' + 2^m = a
        have hval : (a' + 2 ^ m) % 2 ^ (m + 1) = a' + 2 ^ m := by
          apply Nat.mod_eq_of_lt; rw [hpow]; omega
        have heq2 : (a' + 2 ^ m) % 2 ^ (m + 1) = a := by rw [hval]; omega
        exact hfree a' ha' (heq2 ▸ ha)
      · have ha'e : a' % 2 ^ m = a' - 2 ^ m := hmodsub a' ha'H ha'R
        rw [hae, ha'e] at heq
        exact hne (by omega)
  -- Now `card A ≤ card (range (2^m))` via injection.
  have hmaps : ∀ a ∈ A, (fun a => a % 2 ^ m) a ∈ Finset.range (2 ^ m) := by
    intro a _
    simp only [Finset.mem_range]
    exact Nat.mod_lt a (Nat.two_pow_pos m)
  have := Finset.card_le_card_of_injOn (fun a => a % 2 ^ m) hmaps hInj
  simpa [Finset.card_range] using this


end ArkLib.ProximityGap.HalfSumNorm
#print axioms ArkLib.ProximityGap.HalfSumNorm.norm_halfSum_eq
#print axioms ArkLib.ProximityGap.HalfSumNorm.norm_rotated_halfSum_eq
#print axioms ArkLib.ProximityGap.HalfSumNorm.antipodal_pair_sum_zero
#print axioms ArkLib.ProximityGap.HalfSumNorm.antipodal_run_sum_zero
#print axioms ArkLib.ProximityGap.HalfSumNorm.antipodal_symmetric_sum_zero
#print axioms ArkLib.ProximityGap.HalfSumNorm.full_group_sum_eq_zero
#print axioms ArkLib.ProximityGap.HalfSumNorm.norm_halfSum_pow_eq
#print axioms ArkLib.ProximityGap.HalfSumNorm.rootOfUnity_isIntegral
#print axioms ArkLib.ProximityGap.HalfSumNorm.rootPow_sum_isIntegral
#print axioms ArkLib.ProximityGap.HalfSumNorm.norm_rootPow_sum_isIntegral
#print axioms ArkLib.ProximityGap.HalfSumNorm.antipodal_free_card_le
