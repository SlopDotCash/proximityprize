/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the concrete β = 5 (QUINTIC) Thorner–Zaman ladder beyond n = 8 (#466, res:tz-prize-scale)

**Target.**  The explicit-certificate β = 5 ladder discharging the named hypothesis
`TZPrimeSupply n (5 : ℝ) supply` (`KKH26ThornerZaman.lean`) previously existed only at
`n = 8` (`tzPrimeSupply_8_five` in `Frontier/ThornerZamanInstance.lean`, supply 8).  This
file extends the **quintic** ladder to `n ∈ {16, 32, 64} = 2^{4,5,6}`, each with twelve
certified primes:

> **`tzPrimeSupply_{16,32,64}_five`** — `TZPrimeSupply n (5 : ℝ) 12`:
> the window `[n⁵, 2·n⁵]` contains (at least) twelve explicit primes `≡ 1 (mod n)`.

Windows: `n = 16 → [2²⁰, 2²¹]`, `n = 32 → [2²⁵, 2²⁶]`, `n = 64 → [2³⁰, 2³¹]`.

**Why β = 5 (prize relevance).**  The polynomial-field δ* ceiling consumer
`kkh26_mcaDeltaStar_le_of_TZ` needs `β ≥ 3`; higher β enlarges the head-room of the counting
step (`supply ~ n^{β−1−o(1)}` on paper).  Extending the **quintic** ladder past its lone
`n = 8` data point is genuine prize-consumer progress, complementing the landed cubic
(`_ZTZBetaThreeLadderExtension.lean`, up to n = 4096) and β = 2
(`_W16TZPrizeScaleP30.lean`, up to n = 2^30) ladders.

**Certificate technology (mirrors `_W16TZPrizeScaleP30.lean` / `_ZTZBetaThreeLadderExtension.lean`).**
The window primes here are 20–31 bits, sieved deterministically by
`scripts/probes/probe_ztz_beta5_ladder.py` (Miller–Rabin, exact well below 2^64) in the
two-factor Lucas shape

  `p − 1 = 2^e · c`,  `c` an odd prime,

and certified by Mathlib's `lucas_primality` with witness `g = 3` (uniform across all
36 primes): three kernel-cheap modular exponentiations plus a `norm_num` primality check on
the small odd cofactor `c`.  `binaryPow` / `binaryPowAux` / `lucasTwoFactor` are copied
verbatim (with provenance) from the landed `Frontier/_W16TZPrizeScaleP30.lean`, which used
the same pattern at 60 bits; the quintic window arithmetic
(`hpow : (n : ℝ)^(5:ℝ) = n⁵`) mirrors the landed `tzPrimeSupply_8_five` and the cubic ladder.
(Two of the `n = 64` primes — `1073754113`, `1073775617` — reuse the exact factorizations
that appear in the landed cubic ladder, a cross-check of the sieve.)

**Honest scope.**  These are *concrete* discharges of the raw window-cardinality Prop at
β = 5; the asymptotic [TZ24] form (`ThornerZamanPNTinAP`, supply `~ n^{β−1−o(1)}`) and the
named `TZDyadicShortIntervalLB` bookkeeping remain the open analytic input.  This file adds
no axioms and touches no part of the BGK/Paley prize wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 (the consumer).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1 (the analytic source, named Prop).
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_W16TZPrizeScaleP30.lean`,
itself a verbatim copy of the locally verified square-and-multiply from
`Frontier/_PrizeShapePrimeP30.lean`) -/

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

/-! ## The two-factor Lucas certificate (provenance: `Frontier/_W16TZPrizeScaleP30.lean`) -/

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

/-! ## Rung `n = 2^4 = 16`, β = 5 (window `[16⁵, 2·16⁵] = [1048576, 2097152] = [2²⁰, 2²¹]`) -/

private theorem prime_1049057 : Nat.Prime 1049057 :=
  lucasTwoFactor 32783 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1049297 : Nat.Prime 1049297 :=
  lucasTwoFactor 65581 4 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1050593 : Nat.Prime 1050593 :=
  lucasTwoFactor 32831 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1050977 : Nat.Prime 1050977 :=
  lucasTwoFactor 32843 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1051313 : Nat.Prime 1051313 :=
  lucasTwoFactor 65707 4 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1051409 : Nat.Prime 1051409 :=
  lucasTwoFactor 65713 4 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1051697 : Nat.Prime 1051697 :=
  lucasTwoFactor 65731 4 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1052417 : Nat.Prime 1052417 :=
  lucasTwoFactor 4111 8 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1052609 : Nat.Prime 1052609 :=
  lucasTwoFactor 16447 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1052993 : Nat.Prime 1052993 :=
  lucasTwoFactor 16453 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1053089 : Nat.Prime 1053089 :=
  lucasTwoFactor 32909 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1053233 : Nat.Prime 1053233 :=
  lucasTwoFactor 65827 4 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 16`, `β = 5`.**  The window
`[16⁵, 2·16⁵] = [1048576, 2097152]` contains the twelve Lucas-certified primes above,
all `≡ 1 (mod 16)`. -/
theorem tzPrimeSupply_16_five : TZPrimeSupply 16 (5 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((16 : ℕ) : ℝ) ^ (5 : ℝ) = 1048576 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1049057 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1049057, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1049297 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1049297, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1050593 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1050593, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1050977 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1050977, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1051313 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1051313, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1051409 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1051409, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (1051697 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1051697, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (1052417 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1052417, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (1052609 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1052609, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (1052993 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1052993, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (1053089 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1053089, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (1053233 : ℕ) ∈ tzWindow 16 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1053233, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1049057, 1049297, 1050593, 1050977, 1051313, 1051409, 1051697, 1052417,
      1052609, 1052993, 1053089, 1053233} : Finset ℕ) ⊆ tzWindow 16 (5 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1049057, 1049297, 1050593, 1050977, 1051313, 1051409, 1051697, 1052417,
      1052609, 1052993, 1053089, 1053233} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 16 (5 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^5 = 32`, β = 5 (window `[32⁵, 2·32⁵] = [33554432, 67108864] = [2²⁵, 2²⁶]`) -/

private theorem prime_33554849 : Nat.Prime 33554849 :=
  lucasTwoFactor 1048589 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33555617 : Nat.Prime 33555617 :=
  lucasTwoFactor 1048613 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33558689 : Nat.Prime 33558689 :=
  lucasTwoFactor 1048709 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33567713 : Nat.Prime 33567713 :=
  lucasTwoFactor 1048991 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33569633 : Nat.Prime 33569633 :=
  lucasTwoFactor 1049051 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33570689 : Nat.Prime 33570689 :=
  lucasTwoFactor 262271 7 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33573473 : Nat.Prime 33573473 :=
  lucasTwoFactor 1049171 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33579713 : Nat.Prime 33579713 :=
  lucasTwoFactor 524683 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33585569 : Nat.Prime 33585569 :=
  lucasTwoFactor 1049549 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33587969 : Nat.Prime 33587969 :=
  lucasTwoFactor 131203 8 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33588449 : Nat.Prime 33588449 :=
  lucasTwoFactor 1049639 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_33589217 : Nat.Prime 33589217 :=
  lucasTwoFactor 1049663 5 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 32`, `β = 5`.**  The window
`[32⁵, 2·32⁵] = [33554432, 67108864]` contains the twelve Lucas-certified primes above,
all `≡ 1 (mod 32)`. -/
theorem tzPrimeSupply_32_five : TZPrimeSupply 32 (5 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((32 : ℕ) : ℝ) ^ (5 : ℝ) = 33554432 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (33554849 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33554849, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (33555617 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33555617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (33558689 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33558689, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (33567713 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33567713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (33569633 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33569633, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (33570689 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33570689, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (33573473 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33573473, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (33579713 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33579713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (33585569 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33585569, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (33587969 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33587969, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (33588449 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33588449, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (33589217 : ℕ) ∈ tzWindow 32 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_33589217, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      33554849, 33555617, 33558689, 33567713, 33569633, 33570689, 33573473, 33579713,
      33585569, 33587969, 33588449, 33589217} : Finset ℕ) ⊆ tzWindow 32 (5 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      33554849, 33555617, 33558689, 33567713, 33569633, 33570689, 33573473, 33579713,
      33585569, 33587969, 33588449, 33589217} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 32 (5 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^6 = 64`, β = 5 (window `[64⁵, 2·64⁵] = [1073741824, 2147483648] = [2³⁰, 2³¹]`) -/

private theorem prime_1073754113 : Nat.Prime 1073754113 :=
  lucasTwoFactor 262147 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073767169 : Nat.Prime 1073767169 :=
  lucasTwoFactor 4194403 8 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073774657 : Nat.Prime 1073774657 :=
  lucasTwoFactor 16777729 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073775617 : Nat.Prime 1073775617 :=
  lucasTwoFactor 1048609 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073777729 : Nat.Prime 1073777729 :=
  lucasTwoFactor 16777777 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073779649 : Nat.Prime 1073779649 :=
  lucasTwoFactor 16777807 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073800769 : Nat.Prime 1073800769 :=
  lucasTwoFactor 16778137 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073802113 : Nat.Prime 1073802113 :=
  lucasTwoFactor 8389079 7 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073815937 : Nat.Prime 1073815937 :=
  lucasTwoFactor 8389187 7 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073818433 : Nat.Prime 1073818433 :=
  lucasTwoFactor 16778413 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073836097 : Nat.Prime 1073836097 :=
  lucasTwoFactor 16778689 6 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073863937 : Nat.Prime 1073863937 :=
  lucasTwoFactor 4194781 8 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 64`, `β = 5`.**  The window
`[64⁵, 2·64⁵] = [1073741824, 2147483648]` contains the twelve Lucas-certified primes above,
all `≡ 1 (mod 64)`. -/
theorem tzPrimeSupply_64_five : TZPrimeSupply 64 (5 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((64 : ℕ) : ℝ) ^ (5 : ℝ) = 1073741824 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1073754113 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073754113, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1073767169 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073767169, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1073774657 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073774657, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1073775617 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073775617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1073777729 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073777729, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1073779649 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073779649, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (1073800769 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073800769, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (1073802113 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073802113, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (1073815937 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073815937, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (1073818433 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073818433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (1073836097 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073836097, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (1073863937 : ℕ) ∈ tzWindow 64 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073863937, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1073754113, 1073767169, 1073774657, 1073775617, 1073777729, 1073779649, 1073800769,
      1073802113, 1073815937, 1073818433, 1073836097, 1073863937} : Finset ℕ) ⊆ tzWindow 64 (5 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1073754113, 1073767169, 1073774657, 1073775617, 1073777729, 1073779649, 1073800769,
      1073802113, 1073815937, 1073818433, 1073836097, 1073863937} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 64 (5 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_16_five
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_32_five
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFiveLadder.tzPrimeSupply_64_five
