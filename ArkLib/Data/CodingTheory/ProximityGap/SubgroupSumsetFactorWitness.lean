/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetConjecture

/-!
# Generalized witnesses for the BCHKS25 subgroup-sumset conjecture (#389)

The proximity-prize **upper bracket** `1 − ρ − Θ(1/log n)` is gated (BCHKS25 Thm 1.13) on the open
**Conjecture 1.12**: infinitely many primes `q` admit a multiplicative subgroup `G ⊆ F_q^×` of order
`b ≤ 10·log q` whose distinct-element `⌊b/2⌋`-fold sumset covers `≥ q/10` of `F_q`.  The in-tree
witness (`mersenne_admissible`) realizes it for **Mersenne primes** `q = 2^p − 1`, where
`G = ⟨−2⟩` and the `p`-fold signed-power sumset is *all* of `ZMod q`.

This file **strictly enlarges the witness set**: the `⟨−2⟩` covering survives reduction through
*any* prime factor `q ∣ 2^p − 1` (not only `q = 2^p − 1` itself).  Concretely, for `p` an odd prime
and `q` a prime divisor of `2^p − 1`:

* `orderOf_two_eq` — `2` has order exactly `p` in `ZMod q`;
* `two_pow_inj_q`, `two_pow_add_ne_zero_q(')` — the `2p` signed powers `±2^i` (`i < p`) stay
  **distinct** mod `q`;
* `castHom_injOn_signedPowers` — hence the reduction `ZMod (2^p−1) → ZMod q` is injective on them;
* `sumsetDistinct_image` — a distinct-sumset membership transfers through an injective-on-the-set hom;
* **`mem_sumsetDistinct_signedPowers_factor`** — therefore *every* `v ∈ ZMod q` is a sum of `p`
  distinct signed powers, i.e. `G = ⟨−2⟩ ⊆ F_q^×` (order `2p`) has `p`-fold distinct sumset `= F_q`.

So `(q, q, 2p)` is admissible for **every** prime factor `q ≥ 2^{p/5}` of a Mersenne number, not
just Mersenne primes.  (This does **not** prove Conjecture 1.12 — its content is the *infinitude*
of such admissible primes, which remains the open number-theoretic core; it only widens the family
of realized witnesses.)  All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).
-/


open Finset

namespace ArkLib.ProximityGap.SubgroupSumset

/-- Transfer of a distinct-element sumset membership through an additive hom injective on the
ground set. -/
theorem sumsetDistinct_image {F G : Type*} [AddCommMonoid F] [AddCommMonoid G]
    [DecidableEq F] [DecidableEq G] (φ : F →+ G) (E : Finset F) (ℓ : ℕ) {u : F}
    (hu : u ∈ sumsetDistinct E ℓ) (hinj : Set.InjOn φ E) :
    φ u ∈ sumsetDistinct (E.image φ) ℓ := by
  rw [mem_sumsetDistinct] at hu ⊢
  obtain ⟨S, hSE, hScard, hSsum⟩ := hu
  refine ⟨S.image φ, Finset.image_subset_image hSE, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (hinj.mono hSE), hScard]
  · rw [Finset.sum_image (fun a ha b hb h => hinj (hSE ha) (hSE hb) h), ← map_sum, hSsum]

variable {p : ℕ}

/-- In `ZMod q` for a prime `q ∣ 2^p − 1` with `p` prime, `2` has order exactly `p`. -/
theorem orderOf_two_eq {q : ℕ} (hpp : p.Prime) (hq : 1 < q) (hdvd : q ∣ 2 ^ p - 1) :
    orderOf (2 : ZMod q) = p := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨hq⟩
  have h2p : (2 : ZMod q) ^ p = 1 := by
    have hle : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod q) q _).mpr hdvd
    have hsub : (2 : ZMod q) ^ p - 1 = 0 := by
      have e : ((2 ^ p - 1 : ℕ) : ZMod q) = (2 : ZMod q) ^ p - 1 := by
        push_cast [Nat.cast_sub hle]; ring
      rw [← e, hz]
    exact sub_eq_zero.mp hsub
  have hdvdord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h2p
  rcases (Nat.Prime.eq_one_or_self_of_dvd hpp _ hdvdord) with h1 | hp'
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    exact one_ne_zero (show (1 : ZMod q) = 0 by linear_combination h1)
  · exact hp'

variable {q : ℕ}

/-- `2^i = 2^j` in `ZMod q` forces `i = j` for `i, j < p` (from `orderOf 2 = p`). -/
theorem two_pow_inj_q (hpp : p.Prime) (hq : 1 < q) (hdvd : q ∣ 2 ^ p - 1)
    {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : (2 : ZMod q) ^ i = (2 : ZMod q) ^ j) : i = j := by
  have hord := orderOf_two_eq hpp hq hdvd
  exact pow_injOn_Iio_orderOf (by rw [hord]; exact Set.mem_Iio.mpr hi)
    (by rw [hord]; exact Set.mem_Iio.mpr hj) h

/-- `(2 : ZMod q) ≠ 0`: `q` is odd, dividing the odd number `2^p − 1`. -/
theorem q_odd (hp3 : 3 ≤ p) (hq : 1 < q) (hdvd : q ∣ 2 ^ p - 1) :
    (2 : ZMod q) ≠ 0 := by
  haveI : NeZero q := ⟨by omega⟩
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hpp2 : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
    have hm : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
    omega
  intro h2
  have h2n : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h2
  have : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2n
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
  · omega
  · exact hq2 h

/-- `2^i + 2^j ≠ 0` in `ZMod q` for `i ≠ j < p`. -/
theorem two_pow_add_ne_zero_q (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime) (hq : 1 < q)
    (hdvd : q ∣ 2 ^ p - 1) {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    (2 : ZMod q) ^ i + (2 : ZMod q) ^ j ≠ 0 := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact q.Prime := ⟨hqp⟩
  have hord := orderOf_two_eq hpp hq hdvd
  have h2ne : (2 : ZMod q) ≠ 0 := q_odd hp3 hq hdvd
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hpp Nat.prime_two).mpr (by omega)
  have key : ∀ a b : ℕ, b ≤ a → a < p → a ≠ b →
      (2 : ZMod q) ^ a + (2 : ZMod q) ^ b ≠ 0 := by
    intro a b hba ha hab hsum
    have hfac : (2 : ZMod q) ^ b * ((2 : ZMod q) ^ (a - b) + 1) = 0 := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hba]; exact hsum
    have hd1 : (2 : ZMod q) ^ (a - b) + 1 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero _ h2ne)
    have hsq : (2 : ZMod q) ^ (2 * (a - b)) = 1 := by
      rw [two_mul, pow_add, show (2 : ZMod q) ^ (a - b) = -1 by linear_combination hd1]; ring
    have hdvdord : orderOf (2 : ZMod q) ∣ 2 * (a - b) := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hdvdord
    have hpd : p ∣ (a - b) := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvdord
    exact absurd (Nat.le_of_dvd (by omega) hpd) (by omega)
  intro hsum
  rcases le_total j i with hle | hle
  · exact key i j hle hi hij hsum
  · exact key j i hle hj (Ne.symm hij) (by rw [add_comm]; exact hsum)

/-- `2^a + 2^b ≠ 0` in `ZMod q` for **all** `a, b < p` (the `a = b` case uses `2 ≠ 0`). -/
theorem two_pow_add_ne_zero_q' (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime) (hq : 1 < q)
    (hdvd : q ∣ 2 ^ p - 1) {a b : ℕ} (ha : a < p) (hb : b < p) :
    (2 : ZMod q) ^ a + (2 : ZMod q) ^ b ≠ 0 := by
  haveI : Fact q.Prime := ⟨hqp⟩
  have h2ne : (2 : ZMod q) ≠ 0 := q_odd hp3 hq hdvd
  rcases eq_or_ne a b with rfl | hne
  · intro h
    have hz : (2 : ZMod q) ^ a * 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · exact pow_ne_zero a h2ne h'
    · exact h2ne h'
  · exact two_pow_add_ne_zero_q hpp hp3 hqp hq hdvd ha hb hne

/-- The reduction `ZMod (2^p−1) → ZMod q` is **injective on the signed powers** `{±2^i : i<p}`
(they stay distinct mod a prime factor `q`, since `ord_q 2 = p`). -/
theorem castHom_injOn_signedPowers (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime) (hq : 1 < q)
    (hdvd : q ∣ 2 ^ p - 1) :
    Set.InjOn (ZMod.castHom hdvd (ZMod q)) (signedPowers p) := by
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : NeZero q := ⟨by omega⟩
  have hφ2 : ∀ i, (ZMod.castHom hdvd (ZMod q)) ((2 : ZMod (2 ^ p - 1)) ^ i) = (2 : ZMod q) ^ i := by
    intro i; rw [map_pow, map_ofNat]
  intro x hx y hy hxy
  simp only [signedPowers, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe, Finset.mem_range] at hx hy
  rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;>
    simp only [map_neg, map_pow, map_ofNat] at hxy
  · rw [two_pow_inj_q hpp hq hdvd ha hb hxy]
  · exact absurd (show (2 : ZMod q) ^ a + (2 : ZMod q) ^ b = 0 by linear_combination hxy)
      (two_pow_add_ne_zero_q' hpp hp3 hqp hq hdvd ha hb)
  · exact absurd (show (2 : ZMod q) ^ a + (2 : ZMod q) ^ b = 0 by linear_combination -hxy)
      (two_pow_add_ne_zero_q' hpp hp3 hqp hq hdvd ha hb)
  · rw [two_pow_inj_q hpp hq hdvd ha hb (show (2 : ZMod q) ^ a = (2 : ZMod q) ^ b by
      linear_combination -hxy)]

set_option maxHeartbeats 1000000 in
/-- **The `⟨−2⟩` covering over any prime factor of a Mersenne number** (generalizes Remark 7.3
beyond Mersenne *primes*): for a prime `q ∣ 2^p − 1` (`p` an odd prime), every element of
`ZMod q` is the sum of exactly `p` *distinct* signed powers `±2^i` (`i < p`) — i.e. the subgroup
`G = ⟨−2⟩ ⊆ F_q^×` (of order `2p`) has its `p`-fold distinct-element sumset equal to all of `F_q`.
Hence `(q, q, 2p)` is admissible whenever `2p ≤ 10·log q` (i.e. `q ≥ 2^{p/5}`).  This strictly
enlarges the set of BCHKS25 Conj 1.12 witnesses from Mersenne primes to all large prime factors
of Mersenne numbers. -/
theorem mem_sumsetDistinct_signedPowers_factor (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime)
    (hq : 1 < q) (hdvd : q ∣ 2 ^ p - 1) (v : ZMod q) :
    v ∈ sumsetDistinct ((signedPowers p).image (ZMod.castHom hdvd (ZMod q))) p := by
  haveI : NeZero q := ⟨by omega⟩
  set φ := ZMod.castHom hdvd (ZMod q) with hφdef
  have hinj := castHom_injOn_signedPowers hpp hp3 hqp hq hdvd
  have hlift : φ ((v.val : ZMod (2 ^ p - 1))) = v := by
    rw [hφdef, map_natCast]; exact ZMod.natCast_rightInverse v
  obtain ⟨S, hSE, hScard, hSsum⟩ :=
    mem_sumsetDistinct.mp (mem_sumsetDistinct_signedPowers hp3 (v.val : ZMod (2 ^ p - 1)))
  rw [mem_sumsetDistinct]
  refine ⟨S.image φ, Finset.image_subset_image hSE, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (hinj.mono hSE), hScard]
  · rw [Finset.sum_image (fun a ha b hb h => hinj (hSE ha) (hSE hb) h), ← map_sum, hSsum, hlift]

end ArkLib.ProximityGap.SubgroupSumset
