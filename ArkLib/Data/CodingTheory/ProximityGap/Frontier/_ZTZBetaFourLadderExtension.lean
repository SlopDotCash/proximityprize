/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the concrete β = 4 Thorner–Zaman ladder beyond n = 64 (#466, res:tz-prize-scale)

**Target.**  The explicit-certificate **quartic** ladder discharging the named hypothesis
`TZPrimeSupply n (4 : ℝ) supply` (`KKH26ThornerZaman.lean`) previously reached only
`n = 64` at supply 16 (`tzPrimeSupply_64_four` in
`Frontier/ThornerZamanInstance.lean`; the sibling `_TZSubquarticBookkeeping.lean` adds
`n = 128` at supply 12 and `n = 256` at supply 8, both via slow trial-division
`norm_num` primality that does not scale past ~33 bits).  This file lands the
**quartic** ladder uniformly, at the uniform supply 12, at

> **`tzPrimeSupply_{128,256,512,1024}_four`** — `TZPrimeSupply n (4 : ℝ) 12`:
> the window `[n⁴, 2·n⁴]` contains (at least) twelve explicit primes `≡ 1 (mod n)`,
> each Lucas-certified so the certificate cost is logarithmic in `p`, not `√p`.

**Why β = 4 (prize relevance).**  β = 4 is the *analytic-diagonal* exponent: it is the
largest exponent for which the [KKH26] Lemma 2 bad-prime budget stays sub-supply while the
[TZ24] short-interval supply `~ n^{β−1−o(1)}` remains unconditional (`β > 12/5`), and it is
the exponent the polynomial-field δ* ceiling consumer `kkh26_mcaDeltaStar_le_of_TZ` is tuned
to.  The β = 2 ladder cannot feed that consumer (recorded in `_W16TZPrizeScaleP30.lean`);
extending the **quartic** ladder is therefore the most prize-relevant certificate progress.

**Certificate technology (mirrors `_ZTZBetaThreeLadderExtension.lean` /
`_W16TZPrizeScaleP30.lean`).**  The window primes here are 28–41 bits, sieved
deterministically by `scripts/probes/probe_ztz_beta4_ladder.py` (Miller–Rabin, exact well
above `2^41`) in the two-factor Lucas shape

  `p − 1 = 2^e · c`,  `c` an odd prime,

with the probe biased toward **high 2-adic valuation** so every odd cofactor `c` is at most
11 bits (`c ≤ 1933`) — a trivial `norm_num` primality check — while the modulus condition
`p ≡ 1 (mod n)` is automatic from `e ≥ log₂ n`.  Each prime is certified by Mathlib's
`lucas_primality` with witness `g = 3` (uniform across all 48 primes): three kernel-cheap
modular exponentiations plus the small-cofactor primality.  `binaryPow` / `binaryPowAux` /
`lucasTwoFactor` are copied verbatim (with provenance) from the landed
`Frontier/_ZTZBetaThreeLadderExtension.lean`, which used the same pattern; the quartic window
arithmetic (`hpow : (n : ℝ)^(4:ℝ) = n⁴`) mirrors the landed `tzPrimeSupply_64_four`.

**Honest scope.**  These are *concrete* discharges of the raw window-cardinality Prop at
β = 4; the asymptotic [TZ24] form (`ThornerZamanPNTinAP`, supply `~ n^{β−1−o(1)}`) and the
named `TZDyadicShortIntervalLB` bookkeeping (`_TZSubquarticBookkeeping.lean`) remain the
open analytic input.  This file adds no axioms and touches no part of the BGK/Paley prize
wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 (the consumer).  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1 (the analytic source, named Prop).
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_ZTZBetaThreeLadderExtension.lean`,
itself a verbatim copy of the locally verified square-and-multiply from
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
(provenance: `Frontier/_ZTZBetaThreeLadderExtension.lean`) -/

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

/-! ## Rung `n = 2^7 = 128`, β = 4 (window `[n⁴, 2·n⁴] = [268435456, 536870912]`) -/

private theorem prime_270794753 : Nat.Prime 270794753 :=
  lucasTwoFactor 1033 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_274726913 : Nat.Prime 274726913 :=
  lucasTwoFactor 131 21 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_284950529 : Nat.Prime 284950529 :=
  lucasTwoFactor 1087 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290455553 : Nat.Prime 290455553 :=
  lucasTwoFactor 277 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_302252033 : Nat.Prime 302252033 :=
  lucasTwoFactor 1153 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_336068609 : Nat.Prime 336068609 :=
  lucasTwoFactor 641 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_347078657 : Nat.Prime 347078657 :=
  lucasTwoFactor 331 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_376963073 : Nat.Prime 376963073 :=
  lucasTwoFactor 719 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_424148993 : Nat.Prime 424148993 :=
  lucasTwoFactor 809 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_433586177 : Nat.Prime 433586177 :=
  lucasTwoFactor 827 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_469762049 : Nat.Prime 469762049 :=
  lucasTwoFactor 7 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_487063553 : Nat.Prime 487063553 :=
  lucasTwoFactor 929 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 128`, `β = 4`.**  The window
`[128⁴, 2·128⁴] = [268435456, 536870912]` contains the twelve Lucas-certified primes above,
all `≡ 1 (mod 128)`. -/
theorem tzPrimeSupply_128_four : TZPrimeSupply 128 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((128 : ℕ) : ℝ) ^ (4 : ℝ) = 268435456 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (270794753 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_270794753, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (274726913 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_274726913, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (284950529 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_284950529, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (290455553 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290455553, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (302252033 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_302252033, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (336068609 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_336068609, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (347078657 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_347078657, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (376963073 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_376963073, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (424148993 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_424148993, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (433586177 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_433586177, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (469762049 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_469762049, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (487063553 : ℕ) ∈ tzWindow 128 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_487063553, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      270794753, 274726913, 284950529, 290455553, 302252033, 336068609, 347078657, 376963073,
      424148993, 433586177, 469762049, 487063553} : Finset ℕ) ⊆ tzWindow 128 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      270794753, 274726913, 284950529, 290455553, 302252033, 336068609, 347078657, 376963073,
      424148993, 433586177, 469762049, 487063553} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 128 (4 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^8 = 256`, β = 4 (window `[n⁴, 2·n⁴] = [4294967296, 8589934592]`) -/

private theorem prime_4395630593 : Nat.Prime 4395630593 :=
  lucasTwoFactor 131 25 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4483710977 : Nat.Prime 4483710977 :=
  lucasTwoFactor 1069 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4559208449 : Nat.Prime 4559208449 :=
  lucasTwoFactor 1087 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4584374273 : Nat.Prime 4584374273 :=
  lucasTwoFactor 1093 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_5175771137 : Nat.Prime 5175771137 :=
  lucasTwoFactor 617 23 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_5251268609 : Nat.Prime 5251268609 :=
  lucasTwoFactor 313 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_5528092673 : Nat.Prime 5528092673 :=
  lucasTwoFactor 659 23 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_6660554753 : Nat.Prime 6660554753 :=
  lucasTwoFactor 397 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_7063207937 : Nat.Prime 7063207937 :=
  lucasTwoFactor 421 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_7818182657 : Nat.Prime 7818182657 :=
  lucasTwoFactor 233 25 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_7918845953 : Nat.Prime 7918845953 :=
  lucasTwoFactor 59 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_8170504193 : Nat.Prime 8170504193 :=
  lucasTwoFactor 487 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 256`, `β = 4`.**  The window
`[256⁴, 2·256⁴] = [4294967296, 8589934592]` contains the twelve Lucas-certified primes above,
all `≡ 1 (mod 256)`. -/
theorem tzPrimeSupply_256_four : TZPrimeSupply 256 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((256 : ℕ) : ℝ) ^ (4 : ℝ) = 4294967296 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (4395630593 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4395630593, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (4483710977 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4483710977, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (4559208449 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4559208449, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (4584374273 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4584374273, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (5175771137 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_5175771137, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (5251268609 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_5251268609, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (5528092673 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_5528092673, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (6660554753 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_6660554753, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (7063207937 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_7063207937, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (7818182657 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_7818182657, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (7918845953 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_7918845953, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (8170504193 : ℕ) ∈ tzWindow 256 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_8170504193, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      4395630593, 4483710977, 4559208449, 4584374273, 5175771137, 5251268609, 5528092673,
      6660554753, 7063207937, 7818182657, 7918845953, 8170504193} : Finset ℕ)
        ⊆ tzWindow 256 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      4395630593, 4483710977, 4559208449, 4584374273, 5175771137, 5251268609, 5528092673,
      6660554753, 7063207937, 7818182657, 7918845953, 8170504193} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 256 (4 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^9 = 512`, β = 4 (window `[n⁴, 2·n⁴] = [68719476736, 137438953472]`) -/

private theorem prime_69323456513 : Nat.Prime 69323456513 :=
  lucasTwoFactor 1033 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_76369887233 : Nat.Prime 76369887233 :=
  lucasTwoFactor 569 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_78383153153 : Nat.Prime 78383153153 :=
  lucasTwoFactor 73 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_80396419073 : Nat.Prime 80396419073 :=
  lucasTwoFactor 599 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_88852135937 : Nat.Prime 88852135937 :=
  lucasTwoFactor 331 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_96502546433 : Nat.Prime 96502546433 :=
  lucasTwoFactor 719 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_110595407873 : Nat.Prime 110595407873 :=
  lucasTwoFactor 103 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_122675003393 : Nat.Prime 122675003393 :=
  lucasTwoFactor 457 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_126298882049 : Nat.Prime 126298882049 :=
  lucasTwoFactor 941 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_127104188417 : Nat.Prime 127104188417 :=
  lucasTwoFactor 947 27 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_128312147969 : Nat.Prime 128312147969 :=
  lucasTwoFactor 239 29 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_130728067073 : Nat.Prime 130728067073 :=
  lucasTwoFactor 487 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 512`, `β = 4`.**  The window
`[512⁴, 2·512⁴] = [68719476736, 137438953472]` contains the twelve Lucas-certified primes
above, all `≡ 1 (mod 512)`. -/
theorem tzPrimeSupply_512_four : TZPrimeSupply 512 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((512 : ℕ) : ℝ) ^ (4 : ℝ) = 68719476736 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (69323456513 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69323456513, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (76369887233 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_76369887233, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (78383153153 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_78383153153, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (80396419073 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_80396419073, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (88852135937 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_88852135937, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (96502546433 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_96502546433, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (110595407873 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_110595407873, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (122675003393 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_122675003393, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (126298882049 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_126298882049, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (127104188417 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_127104188417, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (128312147969 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_128312147969, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (130728067073 : ℕ) ∈ tzWindow 512 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_130728067073, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      69323456513, 76369887233, 78383153153, 80396419073, 88852135937, 96502546433,
      110595407873, 122675003393, 126298882049, 127104188417, 128312147969, 130728067073}
        : Finset ℕ) ⊆ tzWindow 512 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      69323456513, 76369887233, 78383153153, 80396419073, 88852135937, 96502546433,
      110595407873, 122675003393, 126298882049, 127104188417, 128312147969, 130728067073}
        : Finset ℕ).card := by decide
    _ ≤ (tzWindow 512 (4 : ℝ)).card := Finset.card_le_card hsub

/-! ## Rung `n = 2^10 = 1024`, β = 4 (window `[n⁴, 2·n⁴] = [1099511627776, 2199023255552]`) -/

private theorem prime_1115617755137 : Nat.Prime 1115617755137 :=
  lucasTwoFactor 1039 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1167157362689 : Nat.Prime 1167157362689 :=
  lucasTwoFactor 1087 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1279900254209 : Nat.Prime 1279900254209 :=
  lucasTwoFactor 149 33 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1737314271233 : Nat.Prime 1737314271233 :=
  lucasTwoFactor 809 31 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1859720839169 : Nat.Prime 1859720839169 :=
  lucasTwoFactor 433 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1904817995777 : Nat.Prime 1904817995777 :=
  lucasTwoFactor 887 31 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2001454759937 : Nat.Prime 2001454759937 :=
  lucasTwoFactor 233 33 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2027224563713 : Nat.Prime 2027224563713 :=
  lucasTwoFactor 59 35 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2075542945793 : Nat.Prime 2075542945793 :=
  lucasTwoFactor 1933 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2085206622209 : Nat.Prime 2085206622209 :=
  lucasTwoFactor 971 31 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2098091524097 : Nat.Prime 2098091524097 :=
  lucasTwoFactor 977 31 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_2188285837313 : Nat.Prime 2188285837313 :=
  lucasTwoFactor 1019 31 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for `n = 1024`, `β = 4`.**  The window
`[1024⁴, 2·1024⁴] = [1099511627776, 2199023255552]` contains the twelve Lucas-certified
primes above, all `≡ 1 (mod 1024)`. -/
theorem tzPrimeSupply_1024_four : TZPrimeSupply 1024 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((1024 : ℕ) : ℝ) ^ (4 : ℝ) = 1099511627776 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1115617755137 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1115617755137, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1167157362689 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1167157362689, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1279900254209 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1279900254209, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1737314271233 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1737314271233, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1859720839169 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1859720839169, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1904817995777 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1904817995777, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (2001454759937 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2001454759937, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (2027224563713 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2027224563713, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (2075542945793 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2075542945793, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (2085206622209 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2085206622209, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (2098091524097 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2098091524097, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (2188285837313 : ℕ) ∈ tzWindow 1024 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_2188285837313, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1115617755137, 1167157362689, 1279900254209, 1737314271233, 1859720839169,
      1904817995777, 2001454759937, 2027224563713, 2075542945793, 2085206622209,
      2098091524097, 2188285837313} : Finset ℕ) ⊆ tzWindow 1024 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1115617755137, 1167157362689, 1279900254209, 1737314271233, 1859720839169,
      1904817995777, 2001454759937, 2027224563713, 2075542945793, 2085206622209,
      2098091524097, 2188285837313} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1024 (4 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_128_four
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_256_four
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_512_four
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourLadder.tzPrimeSupply_1024_four
