/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R323ResultantRecurrenceLatticeIndex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R325BinomialRecurrenceReturnBound

/-!
# W12 (#466): `BinomialBadPrimeLaw` is REFUTED — unsatisfiable at every in-window prime

The r323–r331 saturation-route skeleton (kb notes r323/r325/r329) declared exactly ONE
open input, `BinomialBadPrimeLaw`:

> every in-window K-bad prime `p` admits a realized *binomial* kernel relation
> `a + b·x^s` (`|b| < |a|`, realized at `p`: `∃ g, g^{2^k} = −1, a + b·g^s = 0`)
> with `|Res(x^{2^k}+1, a + b·x^s)| ∣ 8p`.

This file proves the law is **unsatisfiable** — not merely false at some exotic endpoint
(r346 refuted one `n = 64` family numerically), but impossible at EVERY prime in the
`n = 32` census window `[n^4, 4n^4] = [2^20, 2^22]` and every prime in the `n = 64`
window `[2^24, 2^26]`, for every badness predicate.  The engine is the exact binomial
resultant closed form, new to the tree:

* `patternResultant_binomial_odd` — for odd `s`:
  `Res(x^{2^k}+1, a + b·x^s) = a^{2^k} + b^{2^k}` exactly (no sign);
* `patternResultant_binomial_even_sq` — for even shifts the resultant is a perfect
  square: `Res(x^{2^{k+1}}+1, a + b·x^{2t}) = Res(x^{2^k}+1, a + b·x^t)^2`.

Both are proved from r323's `patternResultant_cast_eq_prod` by manipulating the product
over the roots of `x^{2^k}+1` in `AlgebraicClosure ℚ` (odd shifts permute the roots;
squaring is 2-to-1 onto the roots one level down).  Combined with FS2's
`charP_dvd_patternResultant_of_common_root` (realization forces `p ∣ Res`), the
arithmetic is airtight:

* odd `s`, `|a| = 2, |b| = 1`: `Res = 2^{2^k} + 1`, which is `< p` (n=32 window) or
  `> 8p` (n=64 window) — either way incompatible with `p ∣ Res ∣ 8p`;
* odd `s`, `|a| ≥ 3`: `Res ≥ 3^{2^k} > 8p`, incompatible with `Res ∣ 8p`;
* even `s`: `Res = E^2` with `p ∣ E`, so `p^2 ∣ Res ∣ 8p`, forcing `p ≤ 8`.

**Numerical companions** (`scripts/probes/probe_w12_binomial_bad_prime_refutation.py`,
`probe_w12_dominant_relation_census.py`): the closed form validated on 120 random cells;
zero realized binomials with `|a| ≤ 4` exist at three census primes; the generalized law
(`|Res| = 2^t·p`, unbounded `t`) has no witness with `|a| ≤ 4096` at ANY of the 92 census
K-bad primes; and the dominant-trinomial repair (`|a| > |b|+|c|`, height ≤ 8) fails at
all 92 census primes and at the r346 `n = 64` endpoint (90/92 have no realized dominant
trinomial at all; the other two have `Res = p^2`, quotient non-dyadic).

**Consequence.**  The r325/r330 master pipe
(`shadowCollisionMass_le_of_span_saturation`) can never be fed at `n ≥ 32` in-window:
its unique open input demands a binomial that provably does not exist.  The saturation
route must replace the single-binomial (or single-dominant) hypothesis by a genuinely
multi-term web/ideal statement, whose return-probability leg the r325 max-coordinate
argument does not cover — that is the honest state of the wall.

Issue #466, thread wall:binomial-bad-prime.
Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial AdjoinRoot

namespace ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted

open ArkLib.ProximityGap.Frontier.FS2PatternAnnihilatorResultant
open ArkLib.ProximityGap.Frontier.R323ResultantRecurrenceLatticeIndex
open ArkLib.ProximityGap.Frontier.R315KernelRelationResultantWeld
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R325BinomialRecurrenceReturnBound

/-! ## §1  The roots of `x^{2^k}+1` in the algebraic closure of ℚ -/

/-- The algebraic closure of ℚ, the ambient field for the root products. -/
abbrev K : Type := AlgebraicClosure ℚ

noncomputable local instance : DecidableEq K := Classical.decEq K

theorem aroots_nodup (k : ℕ) : ((fq k).aroots K).Nodup := by
  rw [Polynomial.aroots_def]
  exact Polynomial.nodup_roots (fq_irreducible k).separable.map

/-- The `2^k` distinct roots of `x^{2^k}+1` in `K`, as a `Finset`. -/
noncomputable def rootFinset (k : ℕ) : Finset K := ((fq k).aroots K).toFinset

theorem aeval_fq (k : ℕ) (y : K) : aeval y (fq k) = y ^ 2 ^ k + 1 := by
  rw [fq, ← algebraMap_int_eq, aeval_map_algebraMap]
  simp [fpoly]

theorem mem_rootFinset {k : ℕ} {y : K} : y ∈ rootFinset k ↔ y ^ 2 ^ k = -1 := by
  rw [rootFinset, Multiset.mem_toFinset, Polynomial.mem_aroots]
  constructor
  · rintro ⟨-, h⟩
    rw [aeval_fq] at h
    linear_combination h
  · intro h
    exact ⟨(fq_monic k).ne_zero, by rw [aeval_fq, h]; ring⟩

theorem card_rootFinset (k : ℕ) : (rootFinset k).card = 2 ^ k := by
  rw [rootFinset, Multiset.toFinset_card_of_nodup (aroots_nodup k), Polynomial.aroots_def]
  have hsp : ((fq k).map (algebraMap ℚ K)).Splits :=
    IsAlgClosed.splits _
  rw [(Polynomial.splits_iff_card_roots).mp hsp, (fq_monic k).natDegree_map, fq_natDegree]

/-- Convert the multiset product over `aroots` into a `Finset` product. -/
theorem prod_aroots_eq_prod_rootFinset (k : ℕ) (f : K → K) :
    (((fq k).aroots K).map f).prod = ∏ y ∈ rootFinset k, f y := by
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  rw [rootFinset, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (aroots_nodup k)]

/-! ## §2  The workhorse: the binomial pattern resultant as a root product -/

theorem cast_patternResultant_binomial (k : ℕ) (a b : ℤ) (s : ℕ) :
    ((patternResultant (2 ^ k) (C a + C b * X ^ s) : ℤ) : K)
      = ∏ y ∈ rootFinset k, ((a : K) + (b : K) * y ^ s) := by
  have h := patternResultant_cast_eq_prod k (C a + C b * X ^ s)
  rw [map_intCast] at h
  rw [h, prod_aroots_eq_prod_rootFinset]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [Polynomial.map_map,
    show (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K from
      RingHom.ext_int _ _]
  simp

/-! ## §3  Odd shifts: `Res = a^{2^k} + b^{2^k}` exactly -/

/-- The linear-factor product over the roots: `∏ (a + b·y) = a^{2^k} + b^{2^k}`. -/
theorem prod_linear_eq (k : ℕ) (hk : 1 ≤ k) (a b : ℤ) (hb : b ≠ 0) :
    ∏ y ∈ rootFinset k, ((a : K) + (b : K) * y) = (a : K) ^ 2 ^ k + (b : K) ^ 2 ^ k := by
  have hbK : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb
  have heven : Even (2 ^ k) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
  set c : K := -(a : K) / (b : K) with hc
  set q : K[X] := (fq k).map (algebraMap ℚ K) with hq
  have hqm : q.Monic := (fq_monic k).map _
  have hqsp : q.Splits := IsAlgClosed.splits q
  -- evaluate q at c two ways
  have he1 : q.eval c = c ^ 2 ^ k + 1 := by
    rw [hq, Polynomial.eval_map, ← aeval_def, aeval_fq]
  have he2 : q.eval c = ∏ y ∈ rootFinset k, (c - y) := by
    conv_lhs => rw [hqsp.eq_prod_roots_of_monic hqm]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    have hmm : (q.roots.map fun y => Polynomial.eval c (X - Polynomial.C y))
        = (q.roots.map fun y => c - y) := Multiset.map_congr rfl fun y _ => by simp
    rw [Function.comp_def, hmm]
    have hqroots : q.roots = (fq k).aroots K := by rw [hq, Polynomial.aroots_def]
    rw [hqroots, prod_aroots_eq_prod_rootFinset]
  have hpoint : ∀ y ∈ rootFinset k, (a : K) + (b : K) * y = (-(b : K)) * (c - y) := by
    intro y _
    rw [hc]
    field_simp
    <;> ring
  rw [Finset.prod_congr rfl hpoint, Finset.prod_mul_distrib, Finset.prod_const,
    card_rootFinset, ← he2, he1, hc, neg_div, heven.neg_pow, heven.neg_pow, div_pow]
  field_simp

/-- For odd `s`, `y ↦ y^s` permutes the roots, so the shifted product collapses. -/
theorem prod_pow_odd_reindex (k : ℕ) {s : ℕ} (hs : Odd s) (a b : ℤ) :
    ∏ y ∈ rootFinset k, ((a : K) + (b : K) * y ^ s)
      = ∏ y ∈ rootFinset k, ((a : K) + (b : K) * y) := by
  have hnd : ¬ (2 ∣ s) := by
    have h1 : s % 2 = 1 := Nat.odd_iff.mp hs
    omega
  have hco : Nat.Coprime s (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _
      (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd))
  obtain ⟨s', _, hs'⟩ := Nat.exists_mul_emod_eq_one_of_coprime hco
    (Nat.one_lt_pow (Nat.succ_ne_zero k) (by norm_num))
  have hss' : s * s' = 2 ^ (k + 1) * (s * s' / 2 ^ (k + 1)) + 1 := by
    conv_lhs => rw [← Nat.div_add_mod (s * s') (2 ^ (k + 1))]
    rw [hs']
  have hodd_ss' : Odd (s * s') := by
    obtain ⟨v, hv⟩ : 2 ∣ 2 ^ (k + 1) * (s * s' / 2 ^ (k + 1)) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero k)) _
    rw [Nat.odd_iff, hss', hv]
    omega
  have hs'odd : Odd s' := (Nat.odd_mul.mp hodd_ss').2
  have hy2m : ∀ y ∈ rootFinset k, y ^ 2 ^ (k + 1) = 1 := by
    intro y hy
    rw [pow_succ, pow_mul, mem_rootFinset.mp hy]
    ring
  have hmaps : ∀ e : ℕ, Odd e → ∀ y ∈ rootFinset k, y ^ e ∈ rootFinset k := by
    intro e he y hy
    rw [mem_rootFinset, ← pow_mul, mul_comm e (2 ^ k), pow_mul, mem_rootFinset.mp hy,
      he.neg_one_pow]
  have hinv : ∀ y ∈ rootFinset k, (y ^ s) ^ s' = y := by
    intro y hy
    rw [← pow_mul, hss', pow_add, pow_mul, hy2m y hy, one_pow, one_mul, pow_one]
  have hinv' : ∀ y ∈ rootFinset k, (y ^ s') ^ s = y := by
    intro y hy
    rw [← pow_mul, mul_comm s' s, hss', pow_add, pow_mul, hy2m y hy, one_pow, one_mul,
      pow_one]
  exact Finset.prod_nbij' (fun y => y ^ s) (fun y => y ^ s')
    (fun y hy => hmaps s hs y hy) (fun y hy => hmaps s' hs'odd y hy)
    (fun y hy => hinv y hy) (fun y hy => hinv' y hy)
    (fun y _ => rfl)

/-- **Closed form, odd shift** (new to the tree): for `k ≥ 1`, `b ≠ 0` and odd `s`,
`Res(x^{2^k}+1, a + b·x^s) = a^{2^k} + b^{2^k}` — exactly, no sign. -/
theorem patternResultant_binomial_odd (k : ℕ) (hk : 1 ≤ k) (a b : ℤ) (hb : b ≠ 0)
    {s : ℕ} (hs : Odd s) :
    patternResultant (2 ^ k) (C a + C b * X ^ s) = a ^ 2 ^ k + b ^ 2 ^ k := by
  have hinj : Function.Injective (Int.cast : ℤ → K) := Int.cast_injective
  apply hinj
  rw [cast_patternResultant_binomial, prod_pow_odd_reindex k hs a b,
    prod_linear_eq k hk a b hb]
  push_cast
  ring

/-! ## §4  Even shifts: the resultant is a perfect square -/

theorem sq_mem_rootFinset {k : ℕ} {y : K} (hy : y ∈ rootFinset (k + 1)) :
    y ^ 2 ∈ rootFinset k := by
  rw [mem_rootFinset, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
  exact mem_rootFinset.mp hy

/-- Each root of `x^{2^k}+1` has exactly two square roots among the roots of
`x^{2^{k+1}}+1`. -/
theorem card_sq_fiber (k : ℕ) {z : K} (hz : z ∈ rootFinset k) :
    (Finset.filter (fun y => y ^ 2 = z) (rootFinset (k + 1))).card = 2 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, y ^ 2 = z :=
    IsAlgClosed.exists_pow_nat_eq z (by norm_num)
  have hz1 : z ^ 2 ^ k = -1 := mem_rootFinset.mp hz
  have hzne : z ≠ 0 := by
    intro h
    rw [h, zero_pow ((pow_pos two_pos k).ne')] at hz1
    exact absurd hz1.symm (by simp)
  have hy0ne : y₀ ≠ 0 := by
    intro h
    apply hzne
    rw [← hy₀, h]
    exact zero_pow (by norm_num)
  have hym : y₀ ∈ rootFinset (k + 1) := by
    rw [mem_rootFinset, show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by ring, pow_mul, hy₀, hz1]
  have hyneg : -y₀ ∈ rootFinset (k + 1) := by
    rw [mem_rootFinset, Even.neg_pow ⟨2 ^ k, by ring⟩]
    exact mem_rootFinset.mp hym
  have hne : y₀ ≠ -y₀ := by
    intro h
    have h2 : y₀ + y₀ = 0 := by linear_combination h
    have h3 : (2 : K) * y₀ = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact two_ne_zero h4
    · exact hy0ne h4
  have hfe : Finset.filter (fun y => y ^ 2 = z) (rootFinset (k + 1)) = {y₀, -y₀} := by
    ext y
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hsq⟩
      have hyy : y * y = y₀ * y₀ := by
        rw [← pow_two, ← pow_two, hsq, hy₀]
      exact mul_self_eq_mul_self_iff.mp hyy
    · rintro (rfl | rfl)
      · exact ⟨hym, hy₀⟩
      · exact ⟨hyneg, by rw [neg_sq]; exact hy₀⟩
  rw [hfe, Finset.card_pair hne]

/-- **Closed form, even shift** (new to the tree): even-shift binomial resultants are
perfect squares — `Res(x^{2^{k+1}}+1, a + b·x^{2t}) = Res(x^{2^k}+1, a + b·x^t)^2`. -/
theorem patternResultant_binomial_even_sq (k : ℕ) (a b : ℤ) (t : ℕ) :
    patternResultant (2 ^ (k + 1)) (C a + C b * X ^ (2 * t))
      = (patternResultant (2 ^ k) (C a + C b * X ^ t)) ^ 2 := by
  have hinj : Function.Injective (Int.cast : ℤ → K) := Int.cast_injective
  apply hinj
  push_cast
  rw [cast_patternResultant_binomial (k + 1) a b (2 * t),
    cast_patternResultant_binomial k a b t]
  have hmaps : ∀ y ∈ rootFinset (k + 1), y ^ 2 ∈ rootFinset k :=
    fun y hy => sq_mem_rootFinset hy
  rw [← Finset.prod_fiberwise_of_maps_to hmaps
    (fun y => (a : K) + (b : K) * y ^ (2 * t))]
  have hinner : ∀ z ∈ rootFinset k,
      (∏ y ∈ Finset.filter (fun y => y ^ 2 = z) (rootFinset (k + 1)),
        ((a : K) + (b : K) * y ^ (2 * t)))
        = ((a : K) + (b : K) * z ^ t) ^ 2 := by
    intro z hz
    have hcongr : ∀ y ∈ Finset.filter (fun y => y ^ 2 = z) (rootFinset (k + 1)),
        (a : K) + (b : K) * y ^ (2 * t) = (a : K) + (b : K) * z ^ t := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [pow_mul, hy.2]
    rw [Finset.prod_congr rfl hcongr, Finset.prod_const, card_sq_fiber k hz]
  rw [Finset.prod_congr rfl hinner, ← Finset.prod_pow]

/-! ## §5  Realization forces `p ∣ Res` -/

theorem prime_dvd_patternResultant_of_realized {p : ℕ} [Fact p.Prime] (k : ℕ)
    (a b : ℤ) (s : ℕ) (g : ZMod p) (hg : g ^ 2 ^ k = -1)
    (hroot : (a : ZMod p) + (b : ZMod p) * g ^ s = 0) :
    (p : ℤ) ∣ patternResultant (2 ^ k) (C a + C b * X ^ s) := by
  refine charP_dvd_patternResultant_of_common_root (by positivity) (ZMod p) p g hg ?_
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_intCast]
  exact hroot

/-! ## §6  The parametric unsatisfiability core -/

/-- **The refutation core.**  At any prime `p > 8` whose window excludes the two binomial
resultant scales (`2^{2^k}+1` on either side, `3^{2^k}` from above), NO realized binomial
relation `a + b·x^s` (`b ≠ 0`, `|b| < |a|`) has `|Res| ∣ 8p`.  This consumes only the
closed form (§3–§4) and realization divisibility (§5). -/
theorem no_realized_binomial_dyadic (k : ℕ) (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime)
    (hp8 : 8 < p)
    (h21 : 2 ^ 2 ^ k + 1 < p ∨ 8 * p < 2 ^ 2 ^ k + 1)
    (h3 : 8 * p < 3 ^ 2 ^ k)
    (a b : ℤ) (hb : b ≠ 0) (hab : |b| < |a|) (s : ℕ) (g : ZMod p)
    (hg : g ^ 2 ^ k = -1)
    (hroot : (a : ZMod p) + (b : ZMod p) * g ^ s = 0)
    (hdvd : (patternResultant (2 ^ k) (C a + C b * X ^ s)).natAbs ∣ 8 * p) : False := by
  haveI := Fact.mk hp
  have hppos : 0 < p := hp.pos
  have hpR : (p : ℤ) ∣ patternResultant (2 ^ k) (C a + C b * X ^ s) :=
    prime_dvd_patternResultant_of_realized k a b s g hg hroot
  have hRle : (patternResultant (2 ^ k) (C a + C b * X ^ s)).natAbs ≤ 8 * p :=
    Nat.le_of_dvd (by omega) hdvd
  have hpN : p ∣ (patternResultant (2 ^ k) (C a + C b * X ^ s)).natAbs := by
    have h1 := Int.natAbs_dvd_natAbs.mpr hpR
    rwa [Int.natAbs_natCast] at h1
  rcases Nat.even_or_odd s with hse | hso
  · -- even shift: the resultant is a perfect square, so p² ∣ Res ∣ 8p — impossible
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨t, ht⟩ := hse
    have h2t : s = 2 * t := by omega
    subst h2t
    have hsq := patternResultant_binomial_even_sq k' a b t
    rw [hsq] at hpR hdvd
    set E := patternResultant (2 ^ k') (C a + C b * X ^ t) with hE
    have hpE : (p : ℤ) ∣ E := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpR
    have hp2 : ((p ^ 2 : ℕ) : ℤ) ∣ E ^ 2 := by
      push_cast
      exact pow_dvd_pow_of_dvd hpE 2
    have hp2N : p ^ 2 ∣ (E ^ 2).natAbs := by
      have h1 := Int.natAbs_dvd_natAbs.mpr hp2
      rwa [Int.natAbs_natCast] at h1
    have hN0 : (E ^ 2).natAbs ≠ 0 := by
      intro h0
      have h8 : 8 * p = 0 := Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd)
      omega
    have hle : (E ^ 2).natAbs ≤ 8 * p := Nat.le_of_dvd (by omega) hdvd
    have hp2le : p ^ 2 ≤ (E ^ 2).natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hp2N
    have hpp : p * p ≤ 8 * p := by
      calc p * p = p ^ 2 := (pow_two p).symm
        _ ≤ (E ^ 2).natAbs := hp2le
        _ ≤ 8 * p := hle
    have : p ≤ 8 := Nat.le_of_mul_le_mul_right hpp hppos
    omega
  · -- odd shift: Res = a^{2^k} + b^{2^k}; both scales are excluded by the window
    have hclosed := patternResultant_binomial_odd k hk a b hb hso
    have heven : Even (2 ^ k) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
    have hcast : ((a.natAbs ^ 2 ^ k + b.natAbs ^ 2 ^ k : ℕ) : ℤ)
        = a ^ 2 ^ k + b ^ 2 ^ k := by
      push_cast [Int.natCast_natAbs]
      rw [heven.pow_abs, heven.pow_abs]
    have hNat : (patternResultant (2 ^ k) (C a + C b * X ^ s)).natAbs
        = a.natAbs ^ 2 ^ k + b.natAbs ^ 2 ^ k := by
      rw [hclosed, ← hcast, Int.natAbs_natCast]
    have hAB : b.natAbs < a.natAbs := by
      have h1 : (b.natAbs : ℤ) < (a.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs]
        exact hab
      exact_mod_cast h1
    have hB1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb
    rw [hNat] at hpN hRle
    rcases Nat.lt_or_ge a.natAbs 3 with hAlt | hAge
    · -- |a| = 2, |b| = 1: Res = 2^{2^k}+1, excluded on both sides by h21
      have hA' : a.natAbs = 2 := by omega
      have hB' : b.natAbs = 1 := by omega
      rw [hA', hB', one_pow] at hpN hRle
      have hple : p ≤ 2 ^ 2 ^ k + 1 := Nat.le_of_dvd (by positivity) hpN
      rcases h21 with h | h
      · exact absurd (lt_of_le_of_lt hple h) (lt_irrefl p)
      · exact absurd (lt_of_le_of_lt hRle h) (lt_irrefl _)
    · -- |a| ≥ 3: Res ≥ 3^{2^k} > 8p, contradicting Res ∣ 8p
      have h3le : 3 ^ 2 ^ k ≤ a.natAbs ^ 2 ^ k := Nat.pow_le_pow_left hAge _
      have hchain : 3 ^ 2 ^ k ≤ 8 * p :=
        le_trans h3le (le_trans (Nat.le_add_right _ _) hRle)
      exact absurd (lt_of_le_of_lt hchain h3) (lt_irrefl _)

/-! ## §7  The two window instantiations (n = 32 and n = 64) -/

/-- **n = 32** (`m = 16`, census window `[n^4, 4n^4] = [2^20, 2^22]`): the
`BinomialBadPrimeLaw` witness is unsatisfiable at EVERY window prime. -/
theorem no_realized_binomial_dyadic_n32 {p : ℕ} (hp : p.Prime)
    (hlo : 2 ^ 20 ≤ p) (hhi : p ≤ 2 ^ 22)
    (a b : ℤ) (hb : b ≠ 0) (hab : |b| < |a|) (s : ℕ) (g : ZMod p)
    (hg : g ^ 2 ^ 4 = -1)
    (hroot : (a : ZMod p) + (b : ZMod p) * g ^ s = 0)
    (hdvd : (patternResultant (2 ^ 4) (C a + C b * X ^ s)).natAbs ∣ 8 * p) : False := by
  have hlo' : 1048576 ≤ p := by norm_num at hlo; exact hlo
  have hhi' : p ≤ 4194304 := by norm_num at hhi; exact hhi
  refine no_realized_binomial_dyadic 4 (by norm_num) hp (by omega) ?_ ?_
    a b hb hab s g hg hroot hdvd
  · left
    norm_num
    omega
  · norm_num
    omega

/-- **n = 64** (`m = 32`, window `[n^4, 4n^4] = [2^24, 2^26]`, contains the r346 K-bad
prime `16778497`): same unsatisfiability. -/
theorem no_realized_binomial_dyadic_n64 {p : ℕ} (hp : p.Prime)
    (hlo : 2 ^ 24 ≤ p) (hhi : p ≤ 2 ^ 26)
    (a b : ℤ) (hb : b ≠ 0) (hab : |b| < |a|) (s : ℕ) (g : ZMod p)
    (hg : g ^ 2 ^ 5 = -1)
    (hroot : (a : ZMod p) + (b : ZMod p) * g ^ s = 0)
    (hdvd : (patternResultant (2 ^ 5) (C a + C b * X ^ s)).natAbs ∣ 8 * p) : False := by
  have hlo' : 16777216 ≤ p := by norm_num at hlo; exact hlo
  have hhi' : p ≤ 67108864 := by norm_num at hhi; exact hhi
  refine no_realized_binomial_dyadic 5 (by norm_num) hp (by omega) ?_ ?_
    a b hb hab s g hg hroot hdvd
  · right
    norm_num
    omega
  · norm_num
    omega

/-! ## §8  The law, stated in the exact campaign vocabulary, and its refutation -/

instance instNeZeroPow (k : ℕ) : NeZero (2 ^ k : ℕ) := ⟨(pow_pos two_pos k).ne'⟩

/-- The binomial vector `a·e₀ + b·e_s` represents the polynomial `a + b·x^s`. -/
theorem relationPoly_binomialVec {m : ℕ} [NeZero m] (a b : ℤ) (s : Fin m) :
    relationPoly (binomialVec a b s) = C a + C b * X ^ (s : ℕ) := by
  classical
  rw [relationPoly]
  have hterm : ∀ j : Fin m, C (binomialVec a b s j) * X ^ (j : ℕ)
      = (if j = 0 then C a * X ^ (j : ℕ) else 0)
        + (if j = s then C b * X ^ (j : ℕ) else 0) := by
    intro j
    simp only [binomialVec]
    split_ifs <;> simp <;> ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin m), Finset.sum_ite_eq' Finset.univ s]
  simp

/-- The evaluation of the binomial vector is `a + b·g^s`. -/
theorem evalVec_binomialVec {F : Type*} [Field F] {m : ℕ} [NeZero m] (g : F)
    (a b : ℤ) (s : Fin m) :
    evalVec g m (binomialVec a b s) = (a : F) + (b : F) * g ^ (s : ℕ) := by
  rw [← aeval_relationPoly, relationPoly_binomialVec]
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_intCast]
  norm_num

/-- **`BinomialBadPrimeLaw`** — the r329/r325 saturation route's single named open
input, stated in the exact vocabulary the route consumes (`binomialVec`,
`relationPoly`, `evalVec`, `patternResultant`; cf. `_R329KernelQuotientOrder.lean`
and kb note r329): every in-window bad prime admits a realized binomial kernel
relation with resultant dividing `8p`. -/
def BinomialBadPrimeLaw (k lo hi : ℕ) (Bad : ℕ → Prop) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    letI := Fact.mk hp
    lo ≤ p → p ≤ hi → Bad p →
    ∃ (a b : ℤ) (s : Fin (2 ^ k)) (g : ZMod p),
      b ≠ 0 ∧ |b| < |a| ∧ g ^ (2 ^ k) = -1 ∧
      evalVec g (2 ^ k) (binomialVec a b s) = 0 ∧
      (patternResultant (2 ^ k) (relationPoly (binomialVec a b s))).natAbs ∣ 8 * p

/-- **REFUTATION, n = 32.**  For EVERY badness predicate, the law forces the window
`[2^20, 2^22]` to contain no bad primes at all — but the #466 depth-4 census exhibits
92 K-bad primes there (`probe_466_d4_structure.py`; e.g. `p = 1065409`).  So the law
can only hold vacuously, and for the actual campaign badness predicate it is false. -/
theorem binomialBadPrimeLaw_n32_forces_no_bad_primes (Bad : ℕ → Prop)
    (hlaw : BinomialBadPrimeLaw 4 (2 ^ 20) (2 ^ 22) Bad) :
    ∀ p : ℕ, p.Prime → 2 ^ 20 ≤ p → p ≤ 2 ^ 22 → ¬ Bad p := by
  intro p hp hlo hhi hbad
  letI := Fact.mk hp
  obtain ⟨a, b, s, g, hb, hab, hg, heval, hdvd⟩ := hlaw p hp hlo hhi hbad
  rw [relationPoly_binomialVec] at hdvd
  rw [evalVec_binomialVec] at heval
  exact no_realized_binomial_dyadic_n32 hp hlo hhi a b hb hab s g hg heval hdvd

/-- **REFUTATION, n = 64.**  Same at the r346 endpoint window `[2^24, 2^26]`. -/
theorem binomialBadPrimeLaw_n64_forces_no_bad_primes (Bad : ℕ → Prop)
    (hlaw : BinomialBadPrimeLaw 5 (2 ^ 24) (2 ^ 26) Bad) :
    ∀ p : ℕ, p.Prime → 2 ^ 24 ≤ p → p ≤ 2 ^ 26 → ¬ Bad p := by
  intro p hp hlo hhi hbad
  letI := Fact.mk hp
  obtain ⟨a, b, s, g, hb, hab, hg, heval, hdvd⟩ := hlaw p hp hlo hhi hbad
  rw [relationPoly_binomialVec] at hdvd
  rw [evalVec_binomialVec] at heval
  exact no_realized_binomial_dyadic_n64 hp hlo hhi a b hb hab s g hg heval hdvd

end ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.patternResultant_binomial_odd
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.patternResultant_binomial_even_sq
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.no_realized_binomial_dyadic
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.no_realized_binomial_dyadic_n32
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.no_realized_binomial_dyadic_n64
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.binomialBadPrimeLaw_n32_forces_no_bad_primes
#print axioms
  ArkLib.ProximityGap.Frontier.W12BinomialBadPrimeRefuted.binomialBadPrimeLaw_n64_forces_no_bad_primes
