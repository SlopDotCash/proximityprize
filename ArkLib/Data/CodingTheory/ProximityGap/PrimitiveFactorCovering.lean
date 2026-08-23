/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveringTransfer

/-!
# Primitive-factor covering: Zsygmondy generalization of the Mersenne witness (#389)

> **`primitiveFactor_signedPowers_covers`** — for odd `m ≥ 3` and a prime `q ∣ 2^m − 1` with
> `ord(2 mod q) = m`, the image of `⟨−2⟩ = signedPowers m` under `ZMod (2^m−1) ↠ ZMod q` has its
> `m`-fold distinct sumset equal to all of `ZMod q`.

Carries the Mersenne `⟨−2⟩` covering to **every** primitive prime factor of `2^m − 1`. Key input:
`castHom_injOn_signedPowers` — for odd `m`, the `2m` signed powers `±2^i` stay distinct mod `q`
(`2^i = −2^j` would force `2^{i−j} = −1`, impossible for odd order). With `CoveringTransfer`. Conj
1.12 then follows from "`∃^∞ m: P(2^m−1) ≥ 2^{m/5}`" (large primitive factor, the open input).
Axiom-clean. Issue #389.
-/

open Finset
open ArkLib.ProximityGap.SubgroupSumset
open ArkLib.ProximityGap.CoveringTransfer

namespace ArkLib.ProximityGap.PrimitiveFactorCovering

variable {m : ℕ} {q : ℕ} [Fact q.Prime]

/-- The reduction `ZMod (2^m − 1) →+* ZMod q` for `q ∣ 2^m − 1`. -/
noncomputable def red (hdvd : q ∣ 2 ^ m - 1) : ZMod (2 ^ m - 1) →+* ZMod q :=
  ZMod.castHom hdvd (ZMod q)

theorem red_two_pow (hdvd : q ∣ 2 ^ m - 1) (i : ℕ) :
    red hdvd ((2 : ZMod (2 ^ m - 1)) ^ i) = (2 : ZMod q) ^ i := by
  simp only [red, map_pow, map_ofNat]

theorem red_surjective (hdvd : q ∣ 2 ^ m - 1) : Function.Surjective (red hdvd) := by
  intro y
  refine ⟨(y.val : ZMod (2 ^ m - 1)), ?_⟩
  simp only [red]
  rw [map_natCast]
  exact ZMod.natCast_rightInverse y

theorem two_ne_zero_zmod (hm1 : 1 ≤ m) (hdvd : q ∣ 2 ^ m - 1) : (2 : ZMod q) ≠ 0 := by
  have hp : q.Prime := Fact.out
  intro h
  have hq2 : q ∣ 2 := by
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    exact (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2
  have hqe : q = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hq2
  subst hqe
  have he : Even (2 ^ m) := (Nat.even_pow (n := m)).mpr ⟨even_two, by omega⟩
  obtain ⟨k, hk⟩ := he
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

/-- **Distinctness mod a primitive factor (odd order).** -/
theorem castHom_injOn_signedPowers (hm : Odd m) (hm3 : 3 ≤ m) (hdvd : q ∣ 2 ^ m - 1)
    (hord : orderOf (2 : ZMod q) = m) :
    Set.InjOn (red hdvd) (signedPowers m) := by
  have hm1 : 1 ≤ m := by rcases hm with ⟨t, rfl⟩; omega
  have h2ne : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hm1 hdvd
  have hnd : ¬ (2 ∣ m) := fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)
  have hcop : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have hpow_inj : ∀ {i j : ℕ}, i < m → j < m →
      (2 : ZMod q) ^ i = (2 : ZMod q) ^ j → i = j := fun {i j} hi hj h =>
    pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; exact hi)
      (by rw [Set.mem_Iio, hord]; exact hj) h
  have hcross : ∀ {i j : ℕ}, i < m → j < m → (2 : ZMod q) ^ i ≠ -(2 : ZMod q) ^ j := by
    intro i j hi hj h
    have hsq : (2 : ZMod q) ^ (2 * i) = (2 : ZMod q) ^ (2 * j) := by
      rw [two_mul i, two_mul j, pow_add, pow_add, h]; ring
    have e1 : (2 : ZMod q) ^ ((2 * i) % m) = (2 : ZMod q) ^ ((2 * j) % m) := by
      rw [← hord, pow_mod_orderOf, pow_mod_orderOf]; exact hsq
    have hmodeq : (2 * i) % m = (2 * j) % m :=
      pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hord]; exact Nat.mod_lt _ hm1)
        (by rw [Set.mem_Iio, hord]; exact Nat.mod_lt _ hm1) e1
    have hij : i = j := Nat.ModEq.eq_of_lt_of_lt
      (Nat.ModEq.cancel_left_of_coprime (Nat.coprime_comm.mp hcop) hmodeq) hi hj
    subst hij
    have hsum : (2 : ZMod q) ^ i * 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp hsum with hh | hh
    · exact pow_ne_zero _ h2ne hh
    · exact h2ne hh
  intro x hx y hy hxy
  rw [mem_coe, mem_signedPowers_iff hm3] at hx hy
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hyj⟩ := hy
  rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl
  · rw [red_two_pow, red_two_pow] at hxy
    rw [hpow_inj hi hj hxy]
  · rw [red_two_pow, map_neg, red_two_pow] at hxy
    exact absurd hxy (hcross hi hj)
  · rw [map_neg, red_two_pow, red_two_pow] at hxy
    exact absurd hxy.symm (hcross hj hi)
  · rw [map_neg, red_two_pow, map_neg, red_two_pow] at hxy
    have : (2 : ZMod q) ^ i = (2 : ZMod q) ^ j := by linear_combination -hxy
    rw [hpow_inj hi hj this]

/-- **Primitive-factor covering.** -/
theorem primitiveFactor_signedPowers_covers (hm : Odd m) (hm3 : 3 ≤ m) (hdvd : q ∣ 2 ^ m - 1)
    (hord : orderOf (2 : ZMod q) = m) :
    sumsetDistinct ((signedPowers m).image (red hdvd)) m = Finset.univ := by
  haveI : NeZero (2 ^ m - 1) := ⟨by have : 1 < 2 ^ m := Nat.one_lt_two_pow_iff.mpr (by omega); omega⟩
  have hcov : sumsetDistinct (signedPowers m) m = Finset.univ :=
    sumsetDistinct_signedPowers_eq_univ hm3
  exact sumsetDistinct_image_eq_univ (red hdvd).toAddMonoidHom (red_surjective hdvd)
    (signedPowers m) m (castHom_injOn_signedPowers hm hm3 hdvd hord) hcov

end ArkLib.ProximityGap.PrimitiveFactorCovering

#print axioms ArkLib.ProximityGap.PrimitiveFactorCovering.primitiveFactor_signedPowers_covers
