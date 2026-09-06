/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the concrete β = 3 Thorner–Zaman ladder beyond n = 256 (#466, res:tz-prize-scale)

**Target.**  The explicit-certificate β = 3 ladder discharging the named hypothesis
`TZPrimeSupply n (3 : ℝ) supply` (`KKH26ThornerZaman.lean`) previously reached only
`n = 256` (`tzPrimeSupply_256_three` in `_TZSubquarticBookkeeping.lean`).  This file
extends the **cubic** ladder to `n ∈ {512, 1024, 2048, 4096} = 2^{9,10,11,12}`:

> **`tzPrimeSupply_{512,1024,2048,4096}_three`** — `TZPrimeSupply n (3 : ℝ) 12`:
> the window `[n³, 2·n³]` contains (at least) twelve explicit primes `≡ 1 (mod n)`.

**Why β = 3 (prize relevance).**  The polynomial-field δ* ceiling consumer
`kkh26_mcaDeltaStar_le_of_TZ` needs `β ≥ 3`; the whole β = 2 certificate ladder
(`tzPrimeSupply_…_two`, up to `n = 2^30` in `_W16TZPrizeScaleP30.lean`) cannot feed it,
as recorded there.  Extending the **cubic** ladder is therefore genuine
prize-consumer progress.

**Certificate technology (mirrors `_W16TZPrizeScaleP30.lean`).**  The window primes here
are 27–37 bits, sieved deterministically by `scripts/probes/probe_ztz_beta3_ladder.py`
(Miller–Rabin, exact below `2^80`) in the two-factor Lucas shape

  `p − 1 = 2^e · c`,  `c` an odd prime,

and certified by Mathlib's `lucas_primality` with witness `g = 3` (uniform across all
48 primes): three kernel-cheap modular exponentiations plus a `norm_num` primality check
on the small odd cofactor `c`.  `binaryPow` / `binaryPowAux` / `lucasTwoFactor` are copied
verbatim (with provenance) from the landed `Frontier/_W16TZPrizeScaleP30.lean`, which used
the same pattern at 60 bits; the cubic window arithmetic
(`hpow : (n : ℝ)^(3:ℝ) = n³`) mirrors the landed `tzPrimeSupply_256_three`.

**Honest scope.**  These are *concrete* discharges of the raw window-cardinality Prop at
β = 3; the asymptotic [TZ24] form (`ThornerZamanPNTinAP`, supply `~ n^{β−1−o(1)}`) and the
named `TZDyadicShortIntervalLB` bookkeeping (`_TZSubquarticBookkeeping.lean`) remain the
open analytic input.  This file adds no axioms and touches no part of the BGK/Paley prize
wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 (the consumer).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1 (the analytic source, named Prop).
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder

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

/-! ## Rung `n = 2^9 = 512`, β = 3 (window `[n³, 2·n³] = [134217728, 268435456]`) -/

private theorem prime_134221313 : Nat.Prime 134221313 :=
  lucasTwoFactor 262151 9 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134242817 : Nat.Prime 134242817 :=
  lucasTwoFactor 262193 9 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134273537 : Nat.Prime 134273537 :=
  lucasTwoFactor 262253 9 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134290433 : Nat.Prime 134290433 :=
  lucasTwoFactor 131143 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134296577 : Nat.Prime 134296577 :=
  lucasTwoFactor 131149 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134336513 : Nat.Prime 134336513 :=
  lucasTwoFactor 32797 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134444033 : Nat.Prime 134444033 :=
  lucasTwoFactor 131293 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134465537 : Nat.Prime 134465537 :=
  lucasTwoFactor 65657 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134473217 : Nat.Prime 134473217 :=
  lucasTwoFactor 262643 9 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134483969 : Nat.Prime 134483969 :=
  lucasTwoFactor 32833 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134520833 : Nat.Prime 134520833 :=
  lucasTwoFactor 16421 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_134588417 : Nat.Prime 134588417 :=
  lucasTwoFactor 65717 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 512`, `β = 3`.**  The window `[512³, 2·512³] = [134217728, 268435456]`
contains the twelve Lucas-certified primes above, all `≡ 1 (mod 512)`. -/
theorem tzPrimeSupply_512_three : TZPrimeSupply 512 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((512 : ℕ) : ℝ) ^ (3 : ℝ) = 134217728 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (134221313 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134221313, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (134242817 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134242817, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (134273537 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134273537, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (134290433 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134290433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (134296577 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134296577, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (134336513 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134336513, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (134444033 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134444033, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (134465537 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134465537, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (134473217 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134473217, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (134483969 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134483969, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (134520833 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134520833, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (134588417 : ℕ) ∈ tzWindow 512 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_134588417, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      134221313, 134242817, 134273537, 134290433, 134296577, 134336513, 134444033, 134465537,
      134473217, 134483969, 134520833, 134588417} : Finset ℕ) ⊆ tzWindow 512 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      134221313, 134242817, 134273537, 134290433, 134296577, 134336513, 134444033, 134465537,
      134473217, 134483969, 134520833, 134588417} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 512 (3 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^10 = 1024`, β = 3 (window `[n³, 2·n³] = [1073741824, 2147483648]`) -/

private theorem prime_1073754113 : Nat.Prime 1073754113 :=
  lucasTwoFactor 262147 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073775617 : Nat.Prime 1073775617 :=
  lucasTwoFactor 1048609 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073907713 : Nat.Prime 1073907713 :=
  lucasTwoFactor 524369 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1073978369 : Nat.Prime 1073978369 :=
  lucasTwoFactor 1048807 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074030593 : Nat.Prime 1074030593 :=
  lucasTwoFactor 524429 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074267137 : Nat.Prime 1074267137 :=
  lucasTwoFactor 1049089 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074316289 : Nat.Prime 1074316289 :=
  lucasTwoFactor 1049137 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074362369 : Nat.Prime 1074362369 :=
  lucasTwoFactor 524591 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074429953 : Nat.Prime 1074429953 :=
  lucasTwoFactor 32789 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074445313 : Nat.Prime 1074445313 :=
  lucasTwoFactor 1049263 10 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074546689 : Nat.Prime 1074546689 :=
  lucasTwoFactor 524681 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1074589697 : Nat.Prime 1074589697 :=
  lucasTwoFactor 262351 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 1024`, `β = 3`.**  The window `[1024³, 2·1024³] = [1073741824, 2147483648]`
contains the twelve Lucas-certified primes above, all `≡ 1 (mod 1024)`. -/
theorem tzPrimeSupply_1024_three : TZPrimeSupply 1024 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((1024 : ℕ) : ℝ) ^ (3 : ℝ) = 1073741824 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1073754113 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073754113, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1073775617 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073775617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1073907713 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073907713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1073978369 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1073978369, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1074030593 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074030593, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1074267137 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074267137, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (1074316289 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074316289, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (1074362369 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074362369, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (1074429953 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074429953, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (1074445313 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074445313, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (1074546689 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074546689, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (1074589697 : ℕ) ∈ tzWindow 1024 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1074589697, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1073754113, 1073775617, 1073907713, 1073978369, 1074030593, 1074267137, 1074316289,
      1074362369, 1074429953, 1074445313, 1074546689, 1074589697} : Finset ℕ) ⊆ tzWindow 1024 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1073754113, 1073775617, 1073907713, 1073978369, 1074030593, 1074267137, 1074316289,
      1074362369, 1074429953, 1074445313, 1074546689, 1074589697} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1024 (3 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^11 = 2048`, β = 3 (window `[n³, 2·n³] = [8589934592, 17179869184]`) -/

private theorem prime_8590108673 : Nat.Prime 8590108673 :=
  lucasTwoFactor 4194389 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8590163969 : Nat.Prime 8590163969 :=
  lucasTwoFactor 262151 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8590391297 : Nat.Prime 8590391297 :=
  lucasTwoFactor 4194527 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591337473 : Nat.Prime 8591337473 :=
  lucasTwoFactor 4194989 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591362049 : Nat.Prime 8591362049 :=
  lucasTwoFactor 4195001 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591620097 : Nat.Prime 8591620097 :=
  lucasTwoFactor 4195127 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591681537 : Nat.Prime 8591681537 :=
  lucasTwoFactor 4195157 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591712257 : Nat.Prime 8591712257 :=
  lucasTwoFactor 1048793 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591835137 : Nat.Prime 8591835137 :=
  lucasTwoFactor 131101 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591915009 : Nat.Prime 8591915009 :=
  lucasTwoFactor 4195271 11 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8591945729 : Nat.Prime 8591945729 :=
  lucasTwoFactor 2097643 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8592007169 : Nat.Prime 8592007169 :=
  lucasTwoFactor 1048829 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 2048`, `β = 3`.**  The window `[2048³, 2·2048³] = [8589934592, 17179869184]`
contains the twelve Lucas-certified primes above, all `≡ 1 (mod 2048)`. -/
theorem tzPrimeSupply_2048_three : TZPrimeSupply 2048 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((2048 : ℕ) : ℝ) ^ (3 : ℝ) = 8589934592 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (8590108673 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8590108673, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (8590163969 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8590163969, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (8590391297 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8590391297, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (8591337473 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591337473, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (8591362049 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591362049, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (8591620097 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591620097, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (8591681537 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591681537, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (8591712257 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591712257, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (8591835137 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591835137, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (8591915009 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591915009, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (8591945729 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8591945729, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (8592007169 : ℕ) ∈ tzWindow 2048 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8592007169, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      8590108673, 8590163969, 8590391297, 8591337473, 8591362049, 8591620097, 8591681537,
      8591712257, 8591835137, 8591915009, 8591945729, 8592007169} : Finset ℕ) ⊆ tzWindow 2048 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      8590108673, 8590163969, 8590391297, 8591337473, 8591362049, 8591620097, 8591681537,
      8591712257, 8591835137, 8591915009, 8591945729, 8592007169} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 2048 (3 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^12 = 4096`, β = 3 (window `[n³, 2·n³] = [68719476736, 137438953472]`) -/

private theorem prime_68720398337 : Nat.Prime 68720398337 :=
  lucasTwoFactor 16777441 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68720422913 : Nat.Prime 68720422913 :=
  lucasTwoFactor 16777447 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68720668673 : Nat.Prime 68720668673 :=
  lucasTwoFactor 16777507 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68720766977 : Nat.Prime 68720766977 :=
  lucasTwoFactor 16777531 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68721037313 : Nat.Prime 68721037313 :=
  lucasTwoFactor 16777597 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68721897473 : Nat.Prime 68721897473 :=
  lucasTwoFactor 16777807 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68722634753 : Nat.Prime 68722634753 :=
  lucasTwoFactor 16777987 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68722782209 : Nat.Prime 68722782209 :=
  lucasTwoFactor 16778023 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68723900417 : Nat.Prime 68723900417 :=
  lucasTwoFactor 2097287 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68725559297 : Nat.Prime 68725559297 :=
  lucasTwoFactor 16778701 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68727648257 : Nat.Prime 68727648257 :=
  lucasTwoFactor 16779211 12 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68728373249 : Nat.Prime 68728373249 :=
  lucasTwoFactor 4194847 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 4096`, `β = 3`.**  The window `[4096³, 2·4096³] = [68719476736, 137438953472]`
contains the twelve Lucas-certified primes above, all `≡ 1 (mod 4096)`. -/
theorem tzPrimeSupply_4096_three : TZPrimeSupply 4096 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((4096 : ℕ) : ℝ) ^ (3 : ℝ) = 68719476736 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (68720398337 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68720398337, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (68720422913 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68720422913, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (68720668673 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68720668673, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (68720766977 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68720766977, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (68721037313 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68721037313, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (68721897473 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68721897473, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (68722634753 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68722634753, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (68722782209 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68722782209, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (68723900417 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68723900417, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (68725559297 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68725559297, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (68727648257 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68727648257, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (68728373249 : ℕ) ∈ tzWindow 4096 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68728373249, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      68720398337, 68720422913, 68720668673, 68720766977, 68721037313, 68721897473,
      68722634753, 68722782209, 68723900417, 68725559297, 68727648257, 68728373249} : Finset ℕ) ⊆ tzWindow 4096 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      68720398337, 68720422913, 68720668673, 68720766977, 68721037313, 68721897473,
      68722634753, 68722782209, 68723900417, 68725559297, 68727648257, 68728373249} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 4096 (3 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_512_three
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_1024_three
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_2048_three
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeLadder.tzPrimeSupply_4096_three
