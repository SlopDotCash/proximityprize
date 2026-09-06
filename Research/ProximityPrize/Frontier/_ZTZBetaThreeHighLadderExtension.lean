/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the concrete β = 3 Thorner–Zaman **high** ladder `n ∈ {8192, 16384}` (#466, res:tz-prize-scale)

**Target.**  The explicit-certificate β = 3 ladder discharging the named hypothesis
`TZPrimeSupply n (3 : ℝ) supply` (`KKH26ThornerZaman.lean`).  The sibling
`_ZTZBetaThreeLadderExtension.lean` pushed the **cubic** ladder up through
`n = 4096 = 2^12`.  This file lands the next two rungs
`n ∈ {8192, 16384} = 2^{13,14}`:

> **`tzPrimeSupply_{8192,16384}_three`** — `TZPrimeSupply n (3 : ℝ) 12`:
> the window `[n³, 2·n³]` contains (at least) twelve explicit primes `≡ 1 (mod n)`.

Windows: `n = 8192 → [8192³, 2·8192³] = [2^39, 2^40] = [549755813888, 1099511627776]`;
`n = 16384 → [16384³, 2·16384³] = [2^42, 2^43] = [4398046511104, 8796093022208]`.

**Why β = 3 (prize relevance).**  The polynomial-field δ* ceiling consumer
`kkh26_mcaDeltaStar_le_of_TZ` needs `β ≥ 3`; the whole β = 2 certificate ladder
(`tzPrimeSupply_…_two`, up to `n = 2^30` in `_W16TZPrizeScaleP30.lean`) cannot feed it,
as recorded there.  Extending the **cubic** ladder is therefore genuine
prize-consumer progress.

**Certificate technology (mirrors `_ZTZBetaThreeLadderExtension.lean` /
`_W16TZPrizeScaleP30.lean`).**  The window primes here are 40–43 bits, sieved
deterministically by `scripts/probes/probe_ztz_beta3_high_ladder.py`
(Miller–Rabin, exact below `3.3·10^24`) in the two-factor Lucas shape

  `p − 1 = 2^e · c`,  `c` an odd prime,

and certified by Mathlib's `lucas_primality` with witness `g = 3` (uniform across all
24 primes): three kernel-cheap modular exponentiations plus a `norm_num` primality check
on the small odd cofactor `c`.  `binaryPow` / `binaryPowAux` / `lucasTwoFactor` are copied
verbatim (with provenance) from the landed `Frontier/_W16TZPrizeScaleP30.lean`, which used
the same pattern at 60 bits; the cubic window arithmetic
(`hpow : (n : ℝ)^(3:ℝ) = n³`) mirrors the landed sibling rungs.

**Honest scope.**  These are *concrete* discharges of the raw window-cardinality Prop at
β = 3; the asymptotic [TZ24] form (`ThornerZamanPNTinAP`, supply `~ n^{β−1−o(1)}`) and the
named `TZDyadicShortIntervalLB` bookkeeping (`_TZSubquarticBookkeeping.lean`) remain the
open analytic input.  This file adds no axioms and touches no part of the BGK/Paley prize
wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 (the consumer).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1 (the analytic source, named Prop).
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder

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

/-! ## Rung `n = 2^13 = 8192`, β = 3 (window `[n³, 2·n³] = [549755813888, 1099511627776]`) -/

private theorem prime_549757198337 : Nat.Prime 549757198337 :=
  lucasTwoFactor 67109033 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549757222913 : Nat.Prime 549757222913 :=
  lucasTwoFactor 16777259 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549757714433 : Nat.Prime 549757714433 :=
  lucasTwoFactor 8388637 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549758451713 : Nat.Prime 549758451713 :=
  lucasTwoFactor 33554593 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549759311873 : Nat.Prime 549759311873 :=
  lucasTwoFactor 67109291 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549760073729 : Nat.Prime 549760073729 :=
  lucasTwoFactor 8388673 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549762359297 : Nat.Prime 549762359297 :=
  lucasTwoFactor 67109663 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549770469377 : Nat.Prime 549770469377 :=
  lucasTwoFactor 67110653 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549770985473 : Nat.Prime 549770985473 :=
  lucasTwoFactor 16777679 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549771501569 : Nat.Prime 549771501569 :=
  lucasTwoFactor 67110779 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549772312577 : Nat.Prime 549772312577 :=
  lucasTwoFactor 33555439 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_549773664257 : Nat.Prime 549773664257 :=
  lucasTwoFactor 67111043 13 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 8192`, `β = 3`.**  The window
`[8192³, 2·8192³] = [549755813888, 1099511627776]` contains the twelve Lucas-certified
primes above, all `≡ 1 (mod 8192)`. -/
theorem tzPrimeSupply_8192_three : TZPrimeSupply 8192 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((8192 : ℕ) : ℝ) ^ (3 : ℝ) = 549755813888 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (549757198337 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549757198337, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (549757222913 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549757222913, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (549757714433 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549757714433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (549758451713 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549758451713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (549759311873 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549759311873, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (549760073729 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549760073729, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (549762359297 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549762359297, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (549770469377 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549770469377, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (549770985473 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549770985473, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (549771501569 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549771501569, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (549772312577 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549772312577, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (549773664257 : ℕ) ∈ tzWindow 8192 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_549773664257, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      549757198337, 549757222913, 549757714433, 549758451713, 549759311873, 549760073729,
      549762359297, 549770469377, 549770985473, 549771501569, 549772312577,
      549773664257} : Finset ℕ) ⊆ tzWindow 8192 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      549757198337, 549757222913, 549757714433, 549758451713, 549759311873, 549760073729,
      549762359297, 549770469377, 549770985473, 549771501569, 549772312577,
      549773664257} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8192 (3 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^14 = 16384`, β = 3 (window `[n³, 2·n³] = [4398046511104, 8796093022208]`) -/

private theorem prime_4398048526337 : Nat.Prime 4398048526337 :=
  lucasTwoFactor 268435579 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398051131393 : Nat.Prime 4398051131393 :=
  lucasTwoFactor 134217869 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398052360193 : Nat.Prime 4398052360193 :=
  lucasTwoFactor 268435813 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398054670337 : Nat.Prime 4398054670337 :=
  lucasTwoFactor 134217977 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398055555073 : Nat.Prime 4398055555073 :=
  lucasTwoFactor 33554501 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398056636417 : Nat.Prime 4398056636417 :=
  lucasTwoFactor 134218037 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398061944833 : Nat.Prime 4398061944833 :=
  lucasTwoFactor 134218199 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398065729537 : Nat.Prime 4398065729537 :=
  lucasTwoFactor 268436629 14 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398069219329 : Nat.Prime 4398069219329 :=
  lucasTwoFactor 134218421 15 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398073643009 : Nat.Prime 4398073643009 :=
  lucasTwoFactor 33554639 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398073839617 : Nat.Prime 4398073839617 :=
  lucasTwoFactor 67109281 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4398081507329 : Nat.Prime 4398081507329 :=
  lucasTwoFactor 33554699 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 16384`, `β = 3`.**  The window
`[16384³, 2·16384³] = [4398046511104, 8796093022208]` contains the twelve Lucas-certified
primes above, all `≡ 1 (mod 16384)`. -/
theorem tzPrimeSupply_16384_three : TZPrimeSupply 16384 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((16384 : ℕ) : ℝ) ^ (3 : ℝ) = 4398046511104 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (4398048526337 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398048526337, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (4398051131393 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398051131393, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (4398052360193 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398052360193, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (4398054670337 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398054670337, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (4398055555073 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398055555073, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (4398056636417 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398056636417, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (4398061944833 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398061944833, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (4398065729537 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398065729537, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (4398069219329 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398069219329, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (4398073643009 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398073643009, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (4398073839617 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398073839617, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (4398081507329 : ℕ) ∈ tzWindow 16384 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4398081507329, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      4398048526337, 4398051131393, 4398052360193, 4398054670337, 4398055555073,
      4398056636417, 4398061944833, 4398065729537, 4398069219329, 4398073643009,
      4398073839617, 4398081507329} : Finset ℕ) ⊆ tzWindow 16384 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      4398048526337, 4398051131393, 4398052360193, 4398054670337, 4398055555073,
      4398056636417, 4398061944833, 4398065729537, 4398069219329, 4398073643009,
      4398073839617, 4398081507329} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 16384 (3 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder.tzPrimeSupply_8192_three
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeHighLadder.tzPrimeSupply_16384_three
