/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetConjecture
import Mathlib.GroupTheory.OrderOfElement

-- The section below threads the four hypotheses `hp hp2 hq hdvd` uniformly via `include`, so a
-- few purely-combinatorial lemmas (e.g. `mem_signedPowersF_iff`) carry unused ones. Disable the
-- unused-section-variable linter file-locally (keeps call sites uniform; no `warning:` lines).
set_option linter.unusedSectionVars false

/-!
# Conjecture 1.12 follows from large prime factors of `2^p − 1` (weaker than Mersenne)

[`SubgroupSumsetConjecture.lean`] states **BCHKS25 Conjecture 1.12** as a named open `Prop`
(`SubgroupSumsetConjecture`) and proves the single Mersenne witness `mersenne_admissible`
(Remark 7.3) over the ring `ZMod (2^p − 1)`. Its docstring asserts — in prose — that
Conjecture 1.12 is *"weaker than the infinitude of Mersenne primes."* This file turns that prose
into a **machine-checked reduction**, and in fact reduces Conjecture 1.12 to a hypothesis
**strictly weaker** than Mersenne primality:

> **`BigOrderTwoPrimeFactorHyp`.** For every `M` there is a prime `q > M` and a prime `p ≥ 12`
> with `q ∣ 2^p − 1` and `2^p ≤ q^4` (equivalently `q ≥ 2^{p/4}`).

i.e. `2^p − 1` has a prime factor `q ≥ 2^{p/4}` for arbitrarily large `q` (with `ord_q(2) = p`
prime). This needs only a *large prime factor* of the Mersenne number `2^p − 1`, **not** its full
primality — every Mersenne prime `q = 2^p − 1` satisfies it with `q^4 ≥ 2^p`, but so does any
prime factor `q ≥ 2^{p/4}` of a composite `2^p − 1`.

## Main result

`subgroupSumsetConjecture_of_bigOrderTwoPrimeFactor :
    BigOrderTwoPrimeFactorHyp → SubgroupSumsetConjecture`.

## The mathematical core

`mem_sumsetDistinct_signedPowersF` — the **signed binary expansion over `F_q`**. When
`q ∣ 2^p − 1` with `p` prime (`p ≠ 2`), `2` has multiplicative order exactly `p` in `F_q^×`, the
subgroup `G = ⟨−2⟩ = {±2^j : j < p}` has `2p` distinct elements, and its `p`-fold distinct sumset
is **all of `F_q`**: every residue `u` mod `q` equals `2·(∑_{i∈T} 2^i)` for the binary digits
`T ⊆ [p)` of `2^{p-1}·u` (a `p`-bit integer, since `q < 2^p`), which is exactly `∑_{i<p} ε_i 2^i`
with `ε_i = ±1`. This ports the covering `mem_sumsetDistinct_signedPowers` from the ring
`ZMod (2^p−1)` to any prime quotient `F_q`, `q ∣ 2^p − 1` — the structural content that makes a
mere large *factor* suffice (the original needed the full Mersenne *number*).

## Honest status

This is a **conditional reduction, NOT a proof of Conjecture 1.12.** The hypothesis
`BigOrderTwoPrimeFactorHyp` is itself open: it is implied by the infinitude of Mersenne primes
but is genuinely weaker, and the best *unconditional* largest-prime-factor bounds for `2^p − 1`
(Stewart) are far below `2^{p/4}`. Conjecture 1.12 stays an open named `Prop`. All proofs here are
axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #389 / #334.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupSumset

/-- The signed powers `{±2^i : i < p}` as a subset of `F_q = ZMod q`. -/
def signedPowersF (q p : ℕ) : Finset (ZMod q) :=
  (Finset.range p).image (fun i => (2 : ZMod q) ^ i) ∪
  (Finset.range p).image (fun i => -(2 : ZMod q) ^ i)

section
variable {p q : ℕ}
  (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1)

include hp hp2 hq hdvd

/-- `q ≠ 2`, since `q ∣ 2^p − 1` which is odd. -/
theorem q_ne_two : q ≠ 2 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hdvd
  have heven : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; have := hp.pos; omega
  have hm1 : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  omega

/-- `(2 : F_q) ≠ 0`. -/
theorem two_ne_zero_F : (2 : ZMod q) ≠ 0 := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hcast : ((2 : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact q_ne_two hp hp2 hq hdvd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  rwa [Nat.cast_ofNat] at hcast

/-- `(2 : F_q)^p = 1`, from `q ∣ 2^p − 1`. -/
theorem two_pow_p_eq_one_F : (2 : ZMod q) ^ p = 1 := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have h0 : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hdvd
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  rw [Nat.cast_sub h1] at h0
  push_cast at h0
  exact sub_eq_zero.mp h0

/-- `2` has multiplicative order exactly `p` in `F_q^×`. -/
theorem orderOf_two_F : orderOf (2 : ZMod q) = p := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd' : orderOf (2 : ZMod q) ∣ p :=
    orderOf_dvd_of_pow_eq_one (two_pow_p_eq_one_F hp hp2 hq hdvd)
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd') with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    exact one_ne_zero (show (1 : ZMod q) = 0 by linear_combination h)
  · exact h

/-- The full geometric sum vanishes: `∑_{i<p} 2^i = 0` in `F_q`. -/
theorem geom_sum_vanishF : ∑ i ∈ Finset.range p, (2 : ZMod q) ^ i = 0 := by
  have hmul := geom_sum_mul (2 : ZMod q) p
  have h21 : (2 : ZMod q) - 1 = 1 := by norm_num
  rw [h21, mul_one, two_pow_p_eq_one_F hp hp2 hq hdvd, sub_self] at hmul
  exact hmul

/-- `2^k = 2^{k mod p}` in `F_q` (cyclic reduction, since `2^p = 1`). -/
theorem two_pow_modF (k : ℕ) :
    (2 : ZMod q) ^ k = (2 : ZMod q) ^ (k % p) := by
  conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul,
    two_pow_p_eq_one_F hp hp2 hq hdvd, one_pow, one_mul]

/-- Injectivity (H1), auxiliary for `i ≤ j`: `2^i = 2^j` forces `i = j`. -/
theorem two_pow_injF_aux {i j : ℕ} (hj : j < p) (hij : i ≤ j)
    (h : (2 : ZMod q) ^ i = (2 : ZMod q) ^ j) : i = j := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_F hp hp2 hq hdvd
  have hpow : (2 : ZMod q) ^ j = (2 : ZMod q) ^ i * (2 : ZMod q) ^ (j - i) := by
    rw [← pow_add]; congr 1; omega
  have hmul : (2 : ZMod q) ^ i * ((2 : ZMod q) ^ (j - i) - 1) = 0 := by
    rw [mul_sub, mul_one, ← hpow]; linear_combination -h
  have hone : (2 : ZMod q) ^ (j - i) = 1 := by
    rcases mul_eq_zero.mp hmul with hz | hz
    · exact absurd hz (pow_ne_zero _ h2)
    · linear_combination hz
  have hord : orderOf (2 : ZMod q) ∣ (j - i) := orderOf_dvd_of_pow_eq_one hone
  rw [orderOf_two_F hp hp2 hq hdvd] at hord
  rcases Nat.eq_zero_or_pos (j - i) with h0 | hp0
  · omega
  · exfalso; have := Nat.le_of_dvd hp0 hord; omega

/-- Injectivity (H1): `2^i = 2^j` in `F_q` forces `i = j` for `i, j < p`. -/
theorem two_pow_injF {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : (2 : ZMod q) ^ i = (2 : ZMod q) ^ j) : i = j := by
  rcases le_total i j with hij | hij
  · exact two_pow_injF_aux hp hp2 hq hdvd hj hij h
  · exact (two_pow_injF_aux hp hp2 hq hdvd hi hij h.symm).symm

/-- Auxiliary (H2 for `j ≤ i`): `2^i + 2^j ≠ 0` in `F_q`. -/
theorem two_pow_add_ne_zeroF_aux {i j : ℕ} (hi : i < p) (hji : j ≤ i) :
    (2 : ZMod q) ^ i + (2 : ZMod q) ^ j ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hsum
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_F hp hp2 hq hdvd
  have hpow : (2 : ZMod q) ^ i = (2 : ZMod q) ^ j * (2 : ZMod q) ^ (i - j) := by
    rw [← pow_add]; congr 1; omega
  have hjne : (2 : ZMod q) ^ j ≠ 0 := pow_ne_zero _ h2
  have hzero : (2 : ZMod q) ^ j * ((2 : ZMod q) ^ (i - j) + 1) = 0 := by
    rw [mul_add, mul_one, ← hpow]; linear_combination hsum
  have hm1 : (2 : ZMod q) ^ (i - j) + 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hjne
    · exact h
  have hm1' : (2 : ZMod q) ^ (i - j) = -1 := by linear_combination hm1
  have hsq : (2 : ZMod q) ^ (2 * (i - j)) = 1 := by
    rw [mul_comm, pow_mul, hm1']; norm_num
  have hord : orderOf (2 : ZMod q) ∣ 2 * (i - j) := orderOf_dvd_of_pow_eq_one hsq
  rw [orderOf_two_F hp hp2 hq hdvd] at hord
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hpij : p ∣ (i - j) := hcop.dvd_of_dvd_mul_left hord
  have hij0 : i - j = 0 := by
    rcases Nat.eq_zero_or_pos (i - j) with h0 | hpos
    · exact h0
    · exfalso; have := Nat.le_of_dvd hpos hpij; omega
  rw [hij0, pow_zero] at hm1'
  exact h2 (by linear_combination hm1')

/-- Injectivity (H2): `2^i + 2^j ≠ 0` in `F_q` for all `i, j < p`. -/
theorem two_pow_add_ne_zeroF {i j : ℕ} (hi : i < p) (hj : j < p) :
    (2 : ZMod q) ^ i + (2 : ZMod q) ^ j ≠ 0 := by
  rcases le_total j i with hji | hij
  · exact two_pow_add_ne_zeroF_aux hp hp2 hq hdvd hi hji
  · rw [add_comm]; exact two_pow_add_ne_zeroF_aux hp hp2 hq hdvd hj hij

/-- Membership characterization of `signedPowersF` (purely combinatorial; no arithmetic). -/
theorem mem_signedPowersF_iff {x : ZMod q} :
    x ∈ signedPowersF q p ↔ ∃ i, i < p ∧ (x = (2 : ZMod q) ^ i
      ∨ x = -(2 : ZMod q) ^ i) := by
  simp only [signedPowersF, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, (rfl | rfl)⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

/-- `signedPowersF` has exactly `2p` elements. -/
theorem signedPowersF_card : (signedPowersF q p).card = 2 * p := by
  have hAinj : Set.InjOn (fun i => (2 : ZMod q) ^ i) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact two_pow_injF hp hp2 hq hdvd (by simpa using ha) (by simpa using hb) hab
  have hBinj : Set.InjOn (fun i => -(2 : ZMod q) ^ i) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact two_pow_injF hp hp2 hq hdvd (by simpa using ha) (by simpa using hb)
      (by linear_combination -hab)
  have hdisj : Disjoint ((Finset.range p).image (fun i => (2 : ZMod q) ^ i))
      ((Finset.range p).image (fun i => -(2 : ZMod q) ^ i)) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA hxB
    obtain ⟨i, hi, rfl⟩ := hxA
    obtain ⟨j, hj, hji⟩ := hxB
    exact two_pow_add_ne_zeroF hp hp2 hq hdvd hi hj (by linear_combination -hji)
  rw [signedPowersF, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hAinj, Finset.card_image_of_injOn hBinj, Finset.card_range]
  omega

/-- `signedPowersF q p` is a multiplicative subgroup of `F_q^×`. -/
theorem isMulSubgroupOf_signedPowersF : IsMulSubgroupOf (signedPowersF q p) := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨?_, ?_, ?_⟩
  · -- 1 ∈ G
    rw [mem_signedPowersF_iff hp hp2 hq hdvd]
    exact ⟨0, hp.pos, Or.inl (by rw [pow_zero])⟩
  · -- 0 ∉ G
    rw [mem_signedPowersF_iff hp hp2 hq hdvd]
    rintro ⟨i, hi, (h | h)⟩
    · exact (pow_ne_zero i (two_ne_zero_F hp hp2 hq hdvd)) h.symm
    · exact (pow_ne_zero i (two_ne_zero_F hp hp2 hq hdvd)) (neg_eq_zero.mp h.symm)
  · -- mul-closed
    intro x hx y hy
    rw [mem_signedPowersF_iff hp hp2 hq hdvd] at hx hy ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    have hmod : (2 : ZMod q) ^ (i + j) = (2 : ZMod q) ^ ((i + j) % p) :=
      two_pow_modF hp hp2 hq hdvd (i + j)
    refine ⟨(i + j) % p, Nat.mod_lt _ hp.pos, ?_⟩
    rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl
    · exact Or.inl (by rw [← pow_add]; exact hmod)
    · exact Or.inr (by rw [mul_neg, ← pow_add, hmod])
    · exact Or.inr (by rw [neg_mul, ← pow_add, hmod])
    · exact Or.inl (by rw [neg_mul_neg, ← pow_add]; exact hmod)

/-- **The covering over `F_q`.** Over `F_q = ZMod q` with `q ∣ 2^p − 1` (`p` prime, `p ≠ 2`),
every element is the sum of exactly `p` *distinct* signed powers `±2^i` (`i < p`). -/
theorem mem_sumsetDistinct_signedPowersF (u : ZMod q) :
    u ∈ sumsetDistinct (signedPowersF q p) p := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  classical
  rw [mem_sumsetDistinct]
  set w : ZMod q := (2 : ZMod q) ^ (p - 1) * u with hw
  have hk : w.val < 2 ^ p := by
    have h1 := ZMod.val_lt w
    have hpos : 0 < 2 ^ p - 1 := by
      have h4 : (4 : ℕ) ≤ 2 ^ p := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
      omega
    have hq2 : q ≤ 2 ^ p - 1 := Nat.le_of_dvd hpos hdvd
    omega
  obtain ⟨T, hTsub, hTsum⟩ := exists_subset_sum_eq p w.val hk
  set e : ℕ → ZMod q :=
    fun i => if i ∈ T then (2 : ZMod q) ^ i else -(2 : ZMod q) ^ i with he
  have einj : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, e i = e j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    simp only [he] at hij
    by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T <;>
      simp only [hiT, hjT, if_true, if_false] at hij
    · exact hne (two_pow_injF hp hp2 hq hdvd hi hj hij)
    · exact two_pow_add_ne_zeroF hp hp2 hq hdvd hi hj (by linear_combination hij)
    · exact two_pow_add_ne_zeroF hp hp2 hq hdvd hj hi (by linear_combination -hij)
    · exact hne (two_pow_injF hp hp2 hq hdvd hi hj (by linear_combination -hij))
  refine ⟨(Finset.range p).image e, ?_, ?_, ?_⟩
  · -- witness set ⊆ signed powers
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [he, signedPowersF, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    by_cases hiT : i ∈ T
    · exact Or.inl ⟨i, hi, by rw [if_pos hiT]⟩
    · exact Or.inr ⟨i, hi, by rw [if_neg hiT]⟩
  · -- exactly p distinct elements
    rw [Finset.card_image_of_injOn
        (fun a ha b hb => einj a (by simpa using ha) b (by simpa using hb)),
      Finset.card_range]
  · -- the sum is u
    rw [Finset.sum_image einj]
    have hrw : ∀ i, e i
        = 2 * (if i ∈ T then (2 : ZMod q) ^ i else 0) - (2 : ZMod q) ^ i := by
      intro i
      simp only [he]
      by_cases h : i ∈ T
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    have hgsum : ∑ i ∈ Finset.range p, (if i ∈ T then (2 : ZMod q) ^ i else 0)
        = ∑ i ∈ T, (2 : ZMod q) ^ i := by
      rw [← Finset.sum_filter]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTsub]
    have hTval : ∑ i ∈ T, (2 : ZMod q) ^ i = w := by
      have hcast : ∑ i ∈ T, (2 : ZMod q) ^ i
          = ((∑ i ∈ T, 2 ^ i : ℕ) : ZMod q) := by push_cast; ring
      rw [hcast, hTsum, ZMod.natCast_zmod_val]
    have h2p : (2 : ZMod q) * (2 : ZMod q) ^ (p - 1) = (2 : ZMod q) ^ p := by
      have hpe : p - 1 + 1 = p := by have := hp.pos; omega
      conv_rhs => rw [← hpe]
      rw [pow_succ']
    rw [Finset.sum_congr rfl (fun i _ => hrw i), Finset.sum_sub_distrib,
      geom_sum_vanishF hp hp2 hq hdvd, sub_zero, ← Finset.mul_sum, hgsum, hTval, hw,
      ← mul_assoc, h2p, two_pow_p_eq_one_F hp hp2 hq hdvd, one_mul]

/-- **Admissibility from a prime factor.** For a prime `q ∣ 2^p − 1` (`p` prime, `p ≠ 2`),
`(q, q/10, 2p)` is admissible: `⟨−2⟩` is a subgroup of order `2p` whose `p`-fold distinct sumset
is *all* of `F_q` (size `q ≥ q/10`). -/
theorem admissible_of_primeFactor : Admissible q (q / 10) (2 * p) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  refine ⟨signedPowersF q p, isMulSubgroupOf_signedPowersF hp hp2 hq hdvd,
    signedPowersF_card hp hp2 hq hdvd, ?_⟩
  have hhalf : 2 * p / 2 = p := by omega
  have hcard : (sumsetDistinct (signedPowersF q p) (2 * p / 2)).card = q := by
    rw [hhalf, Finset.eq_univ_of_forall (mem_sumsetDistinct_signedPowersF hp hp2 hq hdvd),
      Finset.card_univ, ZMod.card]
  rw [hcard]
  exact Nat.div_le_self q 10

end

/-- **The open arithmetic hypothesis** gating the BCHKS25 prize upper bracket — *strictly weaker*
than the infinitude of Mersenne primes. For every `M` there is a prime `q > M` and a prime
`p ≥ 12` with `q ∣ 2^p − 1` and `2^p ≤ q^4` (i.e. `q ≥ 2^{p/4}`). Equivalently: `2^p − 1` has a
prime factor `≥ 2^{p/4}` for arbitrarily large `q` (so `ord_q(2) = p` is prime and `≤ 4 log₂ q`).
This is *implied by* "infinitely many Mersenne primes" (`q = 2^p − 1`, with `q^4 ≥ 2^p`) but does
**not** require `2^p − 1` to be prime, only to have one large prime factor — currently open
(unconditional largest-prime-factor bounds for `2^p − 1` are far below `2^{p/4}`). -/
def BigOrderTwoPrimeFactorHyp : Prop :=
  ∀ M : ℕ, ∃ q : ℕ, M < q ∧ q.Prime ∧
    ∃ p : ℕ, p.Prime ∧ 12 ≤ p ∧ q ∣ 2 ^ p - 1 ∧ 2 ^ p ≤ q ^ 4

/-- **Main reduction.** `BigOrderTwoPrimeFactorHyp ⟹ SubgroupSumsetConjecture` (BCHKS25 Conj 1.12).
A prime factor `q ≥ 2^{p/4}` of `2^p − 1` (`p` prime) gives, via the `⟨−2⟩` signed-binary covering
over `F_q`, an admissible triple `(q, q/10, 2p)` with `2p ≤ 10 log₂ q`. Conjecture 1.12 itself
stays open — this is a conditional reduction onto a (weaker-than-Mersenne but open) hypothesis. -/
theorem subgroupSumsetConjecture_of_bigOrderTwoPrimeFactor
    (H : BigOrderTwoPrimeFactorHyp) : SubgroupSumsetConjecture := by
  intro M
  obtain ⟨q, hMq, hq, p, hp, hp12, hdvd, hbound⟩ := H M
  have hp2 : p ≠ 2 := by omega
  refine ⟨q, hMq, hq, 2 * p, ?_, admissible_of_primeFactor hp hp2 hq hdvd⟩
  -- The bound `2p ≤ 10 · Nat.log 2 q`, derived purely from `2^p ≤ q^4` and `p ≥ 12`.
  set L := Nat.log 2 q with hL
  have hlt : q < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hq4 : q ^ 4 < 2 ^ (4 * (L + 1)) := by
    calc q ^ 4 < (2 ^ (L + 1)) ^ 4 := Nat.pow_lt_pow_left hlt (by norm_num)
      _ = 2 ^ (4 * (L + 1)) := by rw [← pow_mul, Nat.mul_comm]
  have hp4L : 2 ^ p < 2 ^ (4 * (L + 1)) := lt_of_le_of_lt hbound hq4
  have hple : p < 4 * (L + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hp4L
  -- `12 ≤ p < 4(L+1)` ⟹ `L ≥ 3` ⟹ `2p ≤ 8L + 6 ≤ 10L`.
  omega

/-- **Corollary (the Mersenne special case, `q = 2^p − 1`).** The infinitude of Mersenne primes
implies Conjecture 1.12 — `BigOrderTwoPrimeFactorHyp` holds with `q = 2^p − 1` (then `q^4 ≥ 2^p`).
This machine-checks the docstring claim of `SubgroupSumsetConjecture.lean` that Conjecture 1.12 is
"weaker than the infinitude of Mersenne primes". -/
theorem bigOrderTwoPrimeFactor_of_infinitelyManyMersenne
    (H : ∀ M : ℕ, ∃ p : ℕ, M < p ∧ p.Prime ∧ (2 ^ p - 1).Prime) :
    BigOrderTwoPrimeFactorHyp := by
  have key : ∀ x : ℕ, 2 ≤ x → x + 1 ≤ x ^ 4 := by
    intro x hx
    calc x + 1 ≤ x + x := by omega
      _ ≤ x * x := by nlinarith [hx]
      _ = x ^ 2 := by ring
      _ ≤ x ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  intro M
  obtain ⟨p, hMp, hp, hmer⟩ := H (max M 12 + 1)
  have hp12 : 12 ≤ p := by omega
  have h4 : (4 : ℕ) ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
  refine ⟨2 ^ p - 1, ?_, hmer, p, hp, hp12, dvd_refl _, ?_⟩
  · -- M < 2^p - 1
    have hlt : max M 12 + 1 < 2 ^ p := lt_trans hMp (Nat.lt_two_pow_self)
    omega
  · -- 2^p ≤ (2^p - 1)^4
    have hbig : 2 ≤ 2 ^ p - 1 := by omega
    calc 2 ^ p = (2 ^ p - 1) + 1 := by omega
      _ ≤ (2 ^ p - 1) ^ 4 := key _ hbig

end ArkLib.ProximityGap.SubgroupSumset

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.SubgroupSumset.mem_sumsetDistinct_signedPowersF
#print axioms ArkLib.ProximityGap.SubgroupSumset.admissible_of_primeFactor
#print axioms ArkLib.ProximityGap.SubgroupSumset.subgroupSumsetConjecture_of_bigOrderTwoPrimeFactor
#print axioms ArkLib.ProximityGap.SubgroupSumset.bigOrderTwoPrimeFactor_of_infinitelyManyMersenne
