/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# Z-lane — the β = 4 Thorner–Zaman rung AT THE PRIZE MODULUS `n = 2^30` + its δ* ceiling (#466)

**Target.**  `Frontier/_W16TZPrizeScaleP30.lean` landed the prize-modulus rung at `β = 2`
(`[2^60, 2^61]`) and recorded, honestly, that **no** β = 2 ladder can feed the δ* ceiling
consumer — that consumer needs `β ≥ 3`.  This file lands the **quartic** rung at the literal
prize modulus, and cashes it:

> **`tzPrimeSupply_two_pow_30_four`** — `TZPrimeSupply 1073741824 (4 : ℝ) 12`: the window
> `[(2^30)^4, 2·(2^30)^4] = [2^120, 2^121]` contains twelve explicit Lucas-certified
> **121-bit** primes `≡ 1 (mod 2^30)`.
>
> **`kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta4`** — the **first unconditional [KKH26]
> δ* ceiling at the prize domain scale**: a prime `p ≡ 1 (mod 2^30)` with `2^120 ≤ p ≤ 2^121`
> and a smooth domain `⟨g⟩ ⊆ F_p^×` of order `2^30 = |μ_{2^30}|` pin
> `mcaDeltaStar(evalCode g 2^30 0, ε*) ≤ 1/2` for every `ε* < 4/p`.

**Certificate technology.**  Two-factor Lucas at 121 bits: the kernel-cheap
square-and-multiply pattern was proven viable at **158 bits** by the landed
`Frontier/_PrizeShapePrimeP30.lean`; the probe (`scripts/probes/probe_ztz_beta4_prize_scale.py`)
biases toward high 2-adic valuation (`e ∈ [108, 114]`) so every odd cofactor `c ≤ 4951` is an
instant `norm_num` check, and `p ≡ 1 (mod 2^30)` is automatic from `e ≥ 30`.  Witness `g = 3`
uniform across all twelve.  At 121 bits the fixed-base Miller–Rabin screen in the probe is not
the proof — the **Lean kernel Lucas certificate below is**; a screening false-positive would
simply fail here.  `binaryPow`/`binaryPowAux`/`lucasTwoFactor` are copied verbatim (with
provenance) from `Frontier/_ZTZBetaFourLadderExtension.lean`.

**Honest scope.**  (i) The ceiling instance uses `μ = 2`, `r = 2`, so the code is the
degree-0 (`k = 1`) evaluation code on the order-`2^30` domain — the SHAPE of the prize domain
(`p ≡ 1 (mod 2^30)`, `p` prime, smooth subgroup of order `2^30`), not the prize's rate-1/4
code `k = 2^28`, and the ceiling `1/2` is the weakest (r = 2) member of the [KKH26] family.
The μ = 7 tight-ceiling consumer at this modulus needs supply ≈ 4.9·10^8 — far beyond any
explicit-certificate ladder.  (ii) These are concrete discharges of the raw window-cardinality
Prop; the asymptotic [TZ24] form remains the named open analytic input.  (iii) No contact
with the BGK/Paley prize wall.

## References
* [KKH26] ePrint 2026/782, Lemma 2 / Theorem 1.  Issues #334 / #466.
* [TZ24] J. Thorner, A. Zaman, arXiv:2108.10878, Cor 3.1.
-/

namespace ArkLib.ProximityGap.Frontier.ZTZBetaFourPrizeScale

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

/-! ## The twelve 121-bit window primes
(window `[(2^30)^4, 2·(2^30)^4] = [2^120, 2^121]`, all `≡ 1 (mod 2^30)`) -/

private theorem prime_a1 : Nat.Prime 1334095774089792273805554400588988417 :=
  lucasTwoFactor 4111 108 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a2 : Nat.Prime 1477208456253158460316926205663117313 :=
  lucasTwoFactor 569 111 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a3 : Nat.Prime 1499600236455589904464963971082878977 :=
  lucasTwoFactor 4621 108 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a4 : Nat.Prime 1574564022350686478351873011835994113 :=
  lucasTwoFactor 1213 110 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a5 : Nat.Prime 1594035135570192081958862373070569473 :=
  lucasTwoFactor 307 112 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a6 : Nat.Prime 1606691359162870724303405457873043457 :=
  lucasTwoFactor 4951 108 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a7 : Nat.Prime 1751751152648187471175476199070629889 :=
  lucasTwoFactor 2699 109 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a8 : Nat.Prime 1858842275355468291013917685860794369 :=
  lucasTwoFactor 179 113 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a9 : Nat.Prime 1884154722540825575703003855465742337 :=
  lucasTwoFactor 2903 109 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a10 : Nat.Prime 1907520058404232300031391088947232769 :=
  lucasTwoFactor 2939 109 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a11 : Nat.Prime 2596797466374730667718814476651200513 :=
  lucasTwoFactor 4001 109 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_a12 : Nat.Prime 2637686804135692435293492135243808769 :=
  lucasTwoFactor 127 114 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge for the prize modulus `n = 2^30`, `β = 4`.**  The window
`[2^120, 2^121]` contains the twelve Lucas-certified 121-bit primes above, all
`≡ 1 (mod 2^30)`. -/
theorem tzPrimeSupply_two_pow_30_four : TZPrimeSupply 1073741824 (4 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((1073741824 : ℕ) : ℝ) ^ (4 : ℝ) = 1329227995784915872903807060280344576 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

  have h1 : (1334095774089792273805554400588988417 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a1, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h2 : (1477208456253158460316926205663117313 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a2, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h3 : (1499600236455589904464963971082878977 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a3, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h4 : (1574564022350686478351873011835994113 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a4, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h5 : (1594035135570192081958862373070569473 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a5, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h6 : (1606691359162870724303405457873043457 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a6, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h7 : (1751751152648187471175476199070629889 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a7, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h8 : (1858842275355468291013917685860794369 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a8, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h9 : (1884154722540825575703003855465742337 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a9, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h10 : (1907520058404232300031391088947232769 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a10, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h11 : (2596797466374730667718814476651200513 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a11, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have h12 : (2637686804135692435293492135243808769 : ℕ) ∈ tzWindow 1073741824 (4 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_a12, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩

  have hsub : ({
      1334095774089792273805554400588988417, 1477208456253158460316926205663117313,
      1499600236455589904464963971082878977, 1574564022350686478351873011835994113,
      1594035135570192081958862373070569473, 1606691359162870724303405457873043457,
      1751751152648187471175476199070629889, 1858842275355468291013917685860794369,
      1884154722540825575703003855465742337, 1907520058404232300031391088947232769,
      2596797466374730667718814476651200513, 2637686804135692435293492135243808769} : Finset ℕ) ⊆ tzWindow 1073741824 (4 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (12 : ℕ)
      = ({
      1334095774089792273805554400588988417, 1477208456253158460316926205663117313,
      1499600236455589904464963971082878977, 1574564022350686478351873011835994113,
      1594035135570192081958862373070569473, 1606691359162870724303405457873043457,
      1751751152648187471175476199070629889, 1858842275355468291013917685860794369,
      1884154722540825575703003855465742337, 1907520058404232300031391088947232769,
      2596797466374730667718814476651200513, 2637686804135692435293492135243808769} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1073741824 (4 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.Frontier.ZTZBetaFourPrizeScale

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ## The prize-modulus δ* ceiling (mirrors `Frontier/_ZTZBetaFourCeilingWiring.lean`) -/

/-- **The first unconditional [KKH26] δ* ceiling at the prize domain scale.**  A prime
`p ≡ 1 (mod 2^30)` with `2^120 ≤ p ≤ 2^121` and a smooth domain `⟨g⟩ ⊆ F_p^×` of order
`2^30 = |μ_{2^30}|` pin `mcaDeltaStar(evalCode g 2^30 0, ε*) ≤ 1/2` for every `ε* < 4/p`.
End-to-end via `tzPrimeSupply_two_pow_30_four` + `kkh26_mcaDeltaStar_le_of_TZ`.  (Honest
scope: degree-0 code, `r = 2` — the prize-domain SHAPE, not the prize's rate-1/4 code.) -/
theorem kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta4 :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 1073741824] ∧
      ((1073741824 : ℕ) : ℝ) ^ (4 : ℝ) ≤ p ∧
      (p : ℝ) ≤ 2 * ((1073741824 : ℕ) : ℝ) ^ (4 : ℝ) ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = 1073741824 ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ 2 * (2 ^ 1).choose 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g 1073741824 ((2 - 2) * 268435456)) εstar
            ≤ 1 - (2 : ℝ≥0) / ((2 : ℝ≥0) ^ 2) := by
  haveI : NeZero (1073741824 : ℕ) := ⟨by norm_num⟩
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine kkh26_mcaDeltaStar_le_of_TZ
    ArkLib.ProximityGap.Frontier.ZTZBetaFourPrizeScale.tzPrimeSupply_two_pow_30_four
      (μ := 2) (m := 268435456) (r := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [h4, Real.rpow_natCast]; norm_num) (by rw [h4, Real.rpow_natCast]; norm_num) ?_
  -- bad-prime budget: 12 · (4 log2)/(120 log2) = 48/120 = 0.4 < 12
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hc : (collisionPairs 2 2).card = 12 := by decide
  have h16 : Real.log ((((2 : ℕ) ^ 2) ^ 2 ^ (2 - 1) : ℕ) : ℝ) = 4 * Real.log 2 := by
    norm_num
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hden : Real.log (((1073741824 : ℕ) : ℝ) ^ (4 : ℝ)) = 120 * Real.log 2 := by
    rw [Real.log_rpow (by norm_num),
      show ((1073741824 : ℕ) : ℝ) = (2 : ℝ) ^ (30 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [hc, h16, hden, mul_div_mul_right _ _ hlog2]
  norm_num

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.ZTZBetaFourPrizeScale.tzPrimeSupply_two_pow_30_four
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_concrete_prizeModulus_beta4
