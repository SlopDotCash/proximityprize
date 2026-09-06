/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the concrete β = 4 Thorner–Zaman ladder at `n ∈ {2048, 4096}` + its δ* ceilings (#466)

Sibling of `Frontier/_ZTZBetaFourLadderExtension.lean` (which landed
`tzPrimeSupply_{128,256,512,1024}_four`).  This file pushes the **quartic** ladder two more
octaves and, being self-contained over built substrate, wires each new rung straight into the
[KKH26] polynomial-field δ* ceiling consumer:

> **`tzPrimeSupply_{2048,4096}_four`** — `TZPrimeSupply n (4 : ℝ) 12`: the window `[n⁴, 2·n⁴]`
> (`[2⁴⁴, 2⁴⁵]` and `[2⁴⁸, 2⁴⁹]`) contains twelve explicit Lucas-certified primes `≡ 1 (mod n)`.
>
> **`kkh26_mcaDeltaStar_le_concrete_n{2048,4096}_beta4`** — **unconditional** δ* ceilings: a
> prime `p ≡ 1 (mod n)` with `n⁴ ≤ p ≤ 2·n⁴` and a smooth order-`n` domain `⟨g⟩ ⊆ F_p^×` pin
> `mcaDeltaStar(evalCode g n 0, ε*) ≤ 1/2` for every `ε* < 4/p`.

**Certificate technology** mirrors the landed siblings exactly: window primes (44–49 bits)
sieved deterministically by the same Miller–Rabin engine as
`scripts/probes/probe_ztz_beta4_ladder.py` (base set exact far above `2⁴⁹`), biased toward
high 2-adic valuation so every odd cofactor `c ≤ 2309` (instant `norm_num`); each prime
certified by Mathlib's `lucas_primality` with uniform witness `g = 3` in the two-factor shape
`p − 1 = 2^e·c`; `binaryPow`/`binaryPowAux`/`lucasTwoFactor` copied verbatim (with provenance)
from `Frontier/_ZTZBetaFourLadderExtension.lean`.  The ceiling wiring (parameters `μ = 2`,
`r = 2`, `m = n/4`; budget `12·(4 log 2)/(4·log₂n·log 2) = 48/{44,48} < 12`) mirrors
`Frontier/_ZTZBetaFourCeilingWiring.lean`.

**Honest scope.**  Concrete discharges of the raw window-cardinality Prop and its ceiling
consumer at β = 4; the asymptotic [TZ24] form remains the named open analytic input.  No
axioms; no contact with the BGK/Paley prize wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 / Theorem 1.  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1.
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_ZTZBetaFourLadderExtension.lean`,
itself a verbatim copy from `Frontier/_ZTZBetaThreeLadderExtension.lean` /
`Frontier/_W16TZPrizeScaleP30.lean` / `Frontier/_PrizeShapePrimeP30.lean`) -/

/-- Structurally recursive fuel wrapper for kernel-cheap square-and-multiply
exponentiation. -/
private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

/-- Kernel-cheap square-and-multiply exponentiation. -/
private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

/-! ## The two-factor Lucas certificate
(provenance: `Frontier/_ZTZBetaFourLadderExtension.lean`) -/

/-- **Two-factor Lucas certificate.**  If `p − 1 = 2^e · c` with `c` an odd prime, then a
witness `g` with `g^(p−1) = 1`, `g^((p−1)/2) ≠ 1`, `g^((p−1)/c) ≠ 1` certifies `p` prime
(the only prime divisors of `p − 1` are `2` and `c`). -/
private theorem lucasTwoFactor {p : ℕ} (c e : ℕ) (g : ZMod p)
    (hc : Nat.Prime c) (hfact : p - 1 = 2 ^ e * c)
    (hmain : g ^ (p - 1) = 1)
    (h2 : g ^ ((p - 1) / 2) ≠ 1)
    (hcw : g ^ ((p - 1) / c) ≠ 1) : Nat.Prime p := by
  refine lucas_primality p g hmain ?_
  intro q hq hdvd
  rw [hfact] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h2' | hc'
  · obtain rfl : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2')
    exact h2
  · obtain rfl : q = c := (Nat.prime_dvd_prime_iff_eq hq hc).mp hc'
    exact hcw

/-! ## Rung `n = 2^11 = 2048`, β = 4 (window `[n⁴, 2·n⁴] = [17592186044416, 35184372088832]`) -/

private theorem prime_19035295055873 : Nat.Prime 19035295055873 :=
  lucasTwoFactor 277 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_20581483282433 : Nat.Prime 20581483282433 :=
  lucasTwoFactor 599 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_22643067584513 : Nat.Prime 22643067584513 :=
  lucasTwoFactor 659 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_22746146799617 : Nat.Prime 22746146799617 :=
  lucasTwoFactor 331 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_25632364822529 : Nat.Prime 25632364822529 :=
  lucasTwoFactor 373 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_27281632264193 : Nat.Prime 27281632264193 :=
  lucasTwoFactor 397 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_27384711479297 : Nat.Prime 27384711479297 :=
  lucasTwoFactor 797 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_27797028339713 : Nat.Prime 27797028339713 :=
  lucasTwoFactor 809 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_28930899705857 : Nat.Prime 28930899705857 :=
  lucasTwoFactor 421 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_32332513804289 : Nat.Prime 32332513804289 :=
  lucasTwoFactor 941 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33466385170433 : Nat.Prime 33466385170433 :=
  lucasTwoFactor 487 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_35012573396993 : Nat.Prime 35012573396993 :=
  lucasTwoFactor 1019 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 2048`, `β = 4`.**  The window
`[2048⁴, 2·2048⁴] = [17592186044416, 35184372088832]` contains the twelve Lucas-certified
primes above, all `≡ 1 (mod 2048)`. -/
theorem tzPrimeSupply_2048_four : TZPrimeSupply 2048 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((2048 : ℕ) : ℝ) ^ (4 : ℝ) = 17592186044416 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (19035295055873 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_19035295055873, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (20581483282433 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_20581483282433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (22643067584513 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_22643067584513, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (22746146799617 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_22746146799617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (25632364822529 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_25632364822529, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (27281632264193 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_27281632264193, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (27384711479297 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_27384711479297, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (27797028339713 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_27797028339713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (28930899705857 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_28930899705857, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (32332513804289 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_32332513804289, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (33466385170433 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33466385170433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (35012573396993 : ℕ) ∈ tzWindow 2048 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_35012573396993, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      19035295055873, 20581483282433, 22643067584513, 22746146799617, 25632364822529,
      27281632264193, 27384711479297, 27797028339713, 28930899705857, 32332513804289,
      33466385170433, 35012573396993} : Finset ℕ) ⊆ tzWindow 2048 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      19035295055873, 20581483282433, 22643067584513, 22746146799617, 25632364822529,
      27281632264193, 27384711479297, 27797028339713, 28930899705857, 32332513804289,
      33466385170433, 35012573396993} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 2048 (4 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^12 = 4096`, β = 4 (window `[n⁴, 2·n⁴] = [281474976710656, 562949953421312]`) -/

private theorem prime_286010462175233 : Nat.Prime 286010462175233 :=
  lucasTwoFactor 2081 37 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_286422779035649 : Nat.Prime 286422779035649 :=
  lucasTwoFactor 521 39 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_306213988335617 : Nat.Prime 306213988335617 :=
  lucasTwoFactor 557 39 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_312398741241857 : Nat.Prime 312398741241857 :=
  lucasTwoFactor 2273 37 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_312811058102273 : Nat.Prime 312811058102273 :=
  lucasTwoFactor 569 39 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_317346543566849 : Nat.Prime 317346543566849 :=
  lucasTwoFactor 2309 37 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_321057395310593 : Nat.Prime 321057395310593 :=
  lucasTwoFactor 73 42 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_385378825535489 : Nat.Prime 385378825535489 :=
  lucasTwoFactor 701 39 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_420013441810433 : Nat.Prime 420013441810433 :=
  lucasTwoFactor 191 41 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_436506116227073 : Nat.Prime 436506116227073 :=
  lucasTwoFactor 397 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_438980017389569 : Nat.Prime 438980017389569 :=
  lucasTwoFactor 1597 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549480935981057 : Nat.Prime 549480935981057 :=
  lucasTwoFactor 1999 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 4096`, `β = 4`.**  The window
`[4096⁴, 2·4096⁴] = [281474976710656, 562949953421312]` contains the twelve Lucas-certified
primes above, all `≡ 1 (mod 4096)`. -/
theorem tzPrimeSupply_4096_four : TZPrimeSupply 4096 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((4096 : ℕ) : ℝ) ^ (4 : ℝ) = 281474976710656 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (286010462175233 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_286010462175233, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (286422779035649 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_286422779035649, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (306213988335617 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_306213988335617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (312398741241857 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_312398741241857, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (312811058102273 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_312811058102273, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (317346543566849 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_317346543566849, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (321057395310593 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_321057395310593, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (385378825535489 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_385378825535489, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (420013441810433 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_420013441810433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (436506116227073 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_436506116227073, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (438980017389569 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_438980017389569, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (549480935981057 : ℕ) ∈ tzWindow 4096 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549480935981057, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      286010462175233, 286422779035649, 306213988335617, 312398741241857, 312811058102273,
      317346543566849, 321057395310593, 385378825535489, 420013441810433, 436506116227073,
      438980017389569, 549480935981057} : Finset ℕ) ⊆ tzWindow 4096 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      286010462175233, 286422779035649, 306213988335617, 312398741241857, 312811058102273,
      317346543566849, 321057395310593, 385378825535489, 420013441810433, 436506116227073,
      438980017389569, 549480935981057} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 4096 (4 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ## The δ* ceilings (mirrors `Frontier/_ZTZBetaFourCeilingWiring.lean`) -/

/-- **Unconditional [KKH26] δ* ceiling at order 2048, β = 4.**  End-to-end via
`tzPrimeSupply_2048_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n2048_beta4 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2048] ∧
      ((2048 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((2048 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 2048 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 2048 ((2 - 2) * 512)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (2048 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder.tzPrimeSupply_2048_four
      (μ := 2) (m := 512) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(44 log2) = 48/44 ≈ 1.09 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((2048 : ℕ) : ℝ) ^ (4 : ℝ)) = 44 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((2048 : ℕ) : ℝ) = (2 : ℝ) ^ (11 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at order 4096, β = 4.**  End-to-end via
`tzPrimeSupply_4096_four` + `kkh26_mcaDeltaStar_le_of_TZ`. -/
theorem kkh26_mcaDeltaStar_le_concrete_n4096_beta4 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 4096] ∧
      ((4096 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((4096 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 4096 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 4096 ((2 - 2) * 1024)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (4096 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder.tzPrimeSupply_4096_four
      (μ := 2) (m := 1024) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(48 log2) = 48/48 = 1 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((4096 : ℕ) : ℝ) ^ (4 : ℝ)) = 48 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num), show ((4096 : ℕ) : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder.tzPrimeSupply_2048_four
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourHighLadder.tzPrimeSupply_4096_four
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n2048_beta4
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_n4096_beta4
