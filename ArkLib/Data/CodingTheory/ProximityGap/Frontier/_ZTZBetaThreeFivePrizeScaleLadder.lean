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
# Z-lane — β = 3 and β = 5 Thorner–Zaman rungs AT THE PRIZE MODULUS `n = 2^30` + ceilings (#466)

Capstone sibling of `Frontier/_ZTZBetaFourPrizeScaleLadder.lean` (β = 4, `[2^120, 2^121]`).
This file lands the prize-modulus rung at the two remaining ceiling-feeding exponents:

> **`tzPrimeSupply_two_pow_30_three`** — `TZPrimeSupply 1073741824 (3 : ℝ) 12`: the window
> `[(2^30)^3, 2·(2^30)^3] = [2^90, 2^91]` contains twelve explicit Lucas-certified **91-bit**
> primes `≡ 1 (mod 2^30)`.
>
> **`tzPrimeSupply_two_pow_30_five`** — `TZPrimeSupply 1073741824 (5 : ℝ) 12`: the window
> `[2^150, 2^151]` contains twelve explicit Lucas-certified **151-bit** such primes.
>
> **`kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta{3,5}`** — unconditional δ* ceilings at
> the prize domain scale, field sizes `p ≈ 2^90` and `p ≈ 2^150`.

Together with the β = 4 sibling: **the prize-modulus smooth domain `μ_{2^30}` carries an
unconditional sub-capacity [KKH26] δ* ceiling at every polynomial field size
β ∈ {3, 4, 5}** (`p ≈ 2^90, 2^120, 2^150`).

**Certificate technology** as in the siblings (`binaryPow`/`lucasTwoFactor` verbatim with
provenance; probe `scripts/probes/probe_ztz_beta35_prize_scale.py`; cofactors `c ≤ 7537`;
witness `g = 3` uniform; the 151-bit certificates sit below the 158-bit precedent of
`Frontier/_PrizeShapePrimeP30.lean`).

**Honest scope** as in the β = 4 sibling: degree-0 code, `r = 2` — the prize-domain SHAPE,
not the prize's rate-1/4 code; the asymptotic [TZ24] form remains the named open analytic
input; no contact with the BGK/Paley prize wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 / Theorem 1.  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1.
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_ZTZBetaFourPrizeScaleLadder.lean`,
verbatim from `Frontier/_ZTZBetaFourLadderExtension.lean` ← `_ZTZBetaThreeLadderExtension.lean`
← `_W16TZPrizeScaleP30.lean` ← `_PrizeShapePrimeP30.lean`) -/

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
(provenance: `Frontier/_ZTZBetaFourPrizeScaleLadder.lean`) -/

/-- **Two-factor Lucas certificate.**  If `p − 1 = 2^e · c` with `c` an odd prime, then a
witness `g` with `g^(p−1) = 1`, `g^((p−1)/2) ≠ 1`, `g^((p−1)/c) ≠ 1` certifies `p` prime. -/
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

/-! ## β = 3: twelve 91-bit window primes (`[2^90, 2^91]`, all `≡ 1 (mod 2^30)`) -/

private theorem prime_b1 : Nat.Prime 1316822449015234828548702209 :=
  lucasTwoFactor 4357 78 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b2 : Nat.Prime 1324982698297633575477968897 :=
  lucasTwoFactor 137 83 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b3 : Nat.Prime 1334049641944743294288265217 :=
  lucasTwoFactor 2207 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b4 : Nat.Prime 1466427019192545188918591489 :=
  lucasTwoFactor 1213 80 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b5 : Nat.Prime 1729368384958727034417184769 :=
  lucasTwoFactor 2861 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b6 : Nat.Prime 1994123139454330823677837313 :=
  lucasTwoFactor 3299 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b7 : Nat.Prime 2050338190066411080301674497 :=
  lucasTwoFactor 53 85 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b8 : Nat.Prime 2164581680019993537311408129 :=
  lucasTwoFactor 3581 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b9 : Nat.Prime 2195409288420166581266415617 :=
  lucasTwoFactor 227 83 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b10 : Nat.Prime 2237117229196871287793778689 :=
  lucasTwoFactor 3701 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b11 : Nat.Prime 2347733941691609857279393793 :=
  lucasTwoFactor 971 81 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_b12 : Nat.Prime 2364054440256407351137927169 :=
  lucasTwoFactor 3911 79 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for the prize modulus `n = 2^30`, `β = 3`.** -/
theorem tzPrimeSupply_two_pow_30_three : TZPrimeSupply 1073741824 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((1073741824 : ℕ) : ℝ) ^ (3 : ℝ) = 1237940039285380274899124224 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1316822449015234828548702209 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b1, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1324982698297633575477968897 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b2, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1334049641944743294288265217 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b3, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1466427019192545188918591489 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b4, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1729368384958727034417184769 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b5, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1994123139454330823677837313 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b6, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (2050338190066411080301674497 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b7, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (2164581680019993537311408129 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b8, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (2195409288420166581266415617 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b9, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (2237117229196871287793778689 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b10, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (2347733941691609857279393793 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b11, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (2364054440256407351137927169 : ℕ) ∈ tzWindow 1073741824 (3 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_b12, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1316822449015234828548702209, 1324982698297633575477968897,
      1334049641944743294288265217, 1466427019192545188918591489,
      1729368384958727034417184769, 1994123139454330823677837313,
      2050338190066411080301674497, 2164581680019993537311408129,
      2195409288420166581266415617, 2237117229196871287793778689,
      2347733941691609857279393793, 2364054440256407351137927169}
      : Finset ℕ) ⊆ tzWindow 1073741824 (3 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1316822449015234828548702209, 1324982698297633575477968897,
      1334049641944743294288265217, 1466427019192545188918591489,
      1729368384958727034417184769, 1994123139454330823677837313,
      2050338190066411080301674497, 2164581680019993537311408129,
      2195409288420166581266415617, 2237117229196871287793778689,
      2347733941691609857279393793, 2364054440256407351137927169}
      : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1073741824 (3 : ℝ)).card := Finset.card_le_card hsub

/-! ## β = 5: twelve 151-bit window primes (`[2^150, 2^151]`, all `≡ 1 (mod 2^30)`) -/

private theorem prime_c1 : Nat.Prime 1441882556742495602494918784565920623621046273 :=
  lucasTwoFactor 2069 139 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c2 : Nat.Prime 1624818357199192120452828973521239214099791873 :=
  lucasTwoFactor 4663 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c3 : Nat.Prime 1653042737841082440366335116960059796630798337 :=
  lucasTwoFactor 593 141 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c4 : Nat.Prime 1820298326830062113927853004004922507925651457 :=
  lucasTwoFactor 653 141 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c5 : Nat.Prime 1969783009488962697173459615551268556145426433 :=
  lucasTwoFactor 5653 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c6 : Nat.Prime 2074317752607074993149408294954307750704709633 :=
  lucasTwoFactor 5953 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c7 : Nat.Prime 2173625758569281674326559540387194985536028673 :=
  lucasTwoFactor 3119 139 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c8 : Nat.Prime 2254117510770228142228040023527535165346676737 :=
  lucasTwoFactor 6469 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c9 : Nat.Prime 2367015033337789421882064597282817495470702593 :=
  lucasTwoFactor 6793 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c10 : Nat.Prime 2434962616364562414266431238894792971934236673 :=
  lucasTwoFactor 1747 140 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c11 : Nat.Prime 2576084519574014013833961956088895884589268993 :=
  lucasTwoFactor 7393 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_c12 : Nat.Prime 2626261196270707915902417322202354697977724929 :=
  lucasTwoFactor 7537 138 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for the prize modulus `n = 2^30`, `β = 5`.** -/
theorem tzPrimeSupply_two_pow_30_five : TZPrimeSupply 1073741824 (5 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((1073741824 : ℕ) : ℝ) ^ (5 : ℝ) =
      1427247692705959881058285969449495136382746624 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1441882556742495602494918784565920623621046273 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c1, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1624818357199192120452828973521239214099791873 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c2, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1653042737841082440366335116960059796630798337 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c3, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1820298326830062113927853004004922507925651457 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c4, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1969783009488962697173459615551268556145426433 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c5, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (2074317752607074993149408294954307750704709633 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c6, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (2173625758569281674326559540387194985536028673 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c7, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (2254117510770228142228040023527535165346676737 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c8, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (2367015033337789421882064597282817495470702593 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c9, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (2434962616364562414266431238894792971934236673 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c10, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (2576084519574014013833961956088895884589268993 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c11, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (2626261196270707915902417322202354697977724929 : ℕ) ∈
      tzWindow 1073741824 (5 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_c12, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1441882556742495602494918784565920623621046273,
      1624818357199192120452828973521239214099791873,
      1653042737841082440366335116960059796630798337,
      1820298326830062113927853004004922507925651457,
      1969783009488962697173459615551268556145426433,
      2074317752607074993149408294954307750704709633,
      2173625758569281674326559540387194985536028673,
      2254117510770228142228040023527535165346676737,
      2367015033337789421882064597282817495470702593,
      2434962616364562414266431238894792971934236673,
      2576084519574014013833961956088895884589268993,
      2626261196270707915902417322202354697977724929}
      : Finset ℕ) ⊆ tzWindow 1073741824 (5 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1441882556742495602494918784565920623621046273,
      1624818357199192120452828973521239214099791873,
      1653042737841082440366335116960059796630798337,
      1820298326830062113927853004004922507925651457,
      1969783009488962697173459615551268556145426433,
      2074317752607074993149408294954307750704709633,
      2173625758569281674326559540387194985536028673,
      2254117510770228142228040023527535165346676737,
      2367015033337789421882064597282817495470702593,
      2434962616364562414266431238894792971934236673,
      2576084519574014013833961956088895884589268993,
      2626261196270707915902417322202354697977724929}
      : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1073741824 (5 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ## The prize-modulus δ* ceilings at β = 3 and β = 5 -/

/-- **Unconditional [KKH26] δ* ceiling at the prize domain scale, β = 3** (field `p ≈ 2^90`). -/
theorem kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta3 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 1073741824] ∧
      ((1073741824 : ℕ) : ℝ) ^ (3 : ℝ) ≤ p ∧
      (p : ℝ) ≤ 2 * ((1073741824 : ℕ) : ℝ) ^ (3 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 1073741824 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 1073741824 ((2 - 2) * 268435456)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (1073741824 : ℕ) := ⟨by norm_num⟩
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale.tzPrimeSupply_two_pow_30_three
      (μ := 2) (m := 268435456) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h3, Real.rpow_natCast]; norm_num) (by rw [h3, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(90 log2) = 48/90 ≈ 0.53 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((1073741824 : ℕ) : ℝ) ^ (3 : ℝ)) = 90 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num),
      show ((1073741824 : ℕ) : ℝ) = (2 : ℝ) ^ (30 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

/-- **Unconditional [KKH26] δ* ceiling at the prize domain scale, β = 5** (field `p ≈ 2^150`). -/
theorem kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta5 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 1073741824] ∧
      ((1073741824 : ℕ) : ℝ) ^ (5 : ℝ) ≤ p ∧
      (p : ℝ) ≤ 2 * ((1073741824 : ℕ) : ℝ) ^ (5 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 1073741824 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 1073741824 ((2 - 2) * 268435456)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (1073741824 : ℕ) := ⟨by norm_num⟩
  have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale.tzPrimeSupply_two_pow_30_five
      (μ := 2) (m := 268435456) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h5, Real.rpow_natCast]; norm_num) (by rw [h5, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(150 log2) = 48/150 = 0.32 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((1073741824 : ℕ) : ℝ) ^ (5 : ℝ)) = 150 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num),
      show ((1073741824 : ℕ) : ℝ) = (2 : ℝ) ^ (30 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale.tzPrimeSupply_two_pow_30_three
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaThreeFivePrizeScale.tzPrimeSupply_two_pow_30_five
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta3
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta5
