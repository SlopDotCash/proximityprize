/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# W16 — intermediate dyadic `TZPrimeSupply` rungs `n = 2^26 .. 2^29` (#466)

Fills the explicit-certificate Thorner–Zaman ladder between the pre-existing top rung
`n = 2^15` (`ThornerZamanInstance.lean`) and the prize-scale rung `n = 2^30`
(`_W16TZPrizeScaleP30.lean`): for each `k = 26..29` this file proves

  `tzPrimeSupply_<2^k>_two : TZPrimeSupply (2^k) (2 : ℝ) 20`,

i.e. the window `[2^(2k), 2^(2k+1)]` contains at least twenty primes `≡ 1 (mod 2^k)`.
Every witness prime has the kernel-cheap two-factor Lucas shape `p − 1 = 2^a · c`
(`a = max(k, 2k−20)`, `c` an odd prime of ≤ 21 bits, witness `g = 3`), sieved and
independently re-verified by `scripts/probes/probe_w16_tz_prize_scale.py` and emitted
by `scripts/probes/probe_w16_tz_emit_lean.py`.  `binaryPow` is the locally verified
square-and-multiply exponentiation (provenance: `Frontier/_PrizeShapePrimeP30.lean`).

The asymptotic [TZ24] statement remains the named open hypothesis; these are concrete,
axiom-clean discharges at the dyadic moduli, feeding small-supply consumers
(`tzSupplyOne_gives_*`, width-four-refuter-style pigeonholes) at every scale up to the
prize modulus.
-/

namespace ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ArkLib.ProximityGap.KKH26

/-! ## Kernel-cheap exponentiation (provenance: `Frontier/_PrizeShapePrimeP30.lean`,
verbatim copy of the locally verified square-and-multiply implementation) -/

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

/-- **Two-factor Lucas certificate.**  If `p − 1 = 2^e · c` with `c` an odd prime, a
witness `g` with `g^(p−1) = 1`, `g^((p−1)/2) ≠ 1`, `g^((p−1)/c) ≠ 1` certifies `p`
prime. -/
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

/-! ### Rung `n = 2^26 = 67108864`: window `[4503599627370496, 9007199254740992]` -/

private theorem prime_4504591764815873 : Nat.Prime 4504591764815873 :=
  lucasTwoFactor 1048807 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4505983334219777 : Nat.Prime 4505983334219777 :=
  lucasTwoFactor 1049131 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4506163722846209 : Nat.Prime 4506163722846209 :=
  lucasTwoFactor 1049173 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4507684141268993 : Nat.Prime 4507684141268993 :=
  lucasTwoFactor 1049527 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4507709911072769 : Nat.Prime 4507709911072769 :=
  lucasTwoFactor 1049533 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4508457235382273 : Nat.Prime 4508457235382273 :=
  lucasTwoFactor 1049707 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4508972631457793 : Nat.Prime 4508972631457793 :=
  lucasTwoFactor 1049827 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4509848804786177 : Nat.Prime 4509848804786177 :=
  lucasTwoFactor 1050031 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4511034215759873 : Nat.Prime 4511034215759873 :=
  lucasTwoFactor 1050307 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4511523842031617 : Nat.Prime 4511523842031617 :=
  lucasTwoFactor 1050421 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4512838102024193 : Nat.Prime 4512838102024193 :=
  lucasTwoFactor 1050727 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4513070030258177 : Nat.Prime 4513070030258177 :=
  lucasTwoFactor 1050781 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4513997743194113 : Nat.Prime 4513997743194113 :=
  lucasTwoFactor 1050997 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4514358520446977 : Nat.Prime 4514358520446977 :=
  lucasTwoFactor 1051081 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4515260463579137 : Nat.Prime 4515260463579137 :=
  lucasTwoFactor 1051291 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4517090119647233 : Nat.Prime 4517090119647233 :=
  lucasTwoFactor 1051717 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4521754454130689 : Nat.Prime 4521754454130689 :=
  lucasTwoFactor 1052803 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4525104528621569 : Nat.Prime 4525104528621569 :=
  lucasTwoFactor 1053583 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4526109550968833 : Nat.Prime 4526109550968833 :=
  lucasTwoFactor 1053817 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4526856875278337 : Nat.Prime 4526856875278337 :=
  lucasTwoFactor 1053991 32 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^26 = 67108864`, `β = 2`.**
The window `[67108864², 2·67108864²] = [4503599627370496, 9007199254740992]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 67108864)`. -/
theorem tzPrimeSupply_67108864_two : TZPrimeSupply 67108864 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((67108864 : ℕ) : ℝ) ^ (2 : ℝ) = 4503599627370496 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (4504591764815873 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4504591764815873, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (4505983334219777 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4505983334219777, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (4506163722846209 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4506163722846209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (4507684141268993 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4507684141268993, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (4507709911072769 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4507709911072769, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (4508457235382273 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4508457235382273, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (4508972631457793 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4508972631457793, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (4509848804786177 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4509848804786177, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (4511034215759873 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4511034215759873, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (4511523842031617 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4511523842031617, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (4512838102024193 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4512838102024193, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (4513070030258177 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4513070030258177, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (4513997743194113 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4513997743194113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (4514358520446977 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4514358520446977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (4515260463579137 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4515260463579137, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (4517090119647233 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4517090119647233, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (4521754454130689 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4521754454130689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (4525104528621569 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4525104528621569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (4526109550968833 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4526109550968833, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (4526856875278337 : ℕ) ∈ tzWindow 67108864 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4526856875278337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({4504591764815873, 4505983334219777, 4506163722846209,
        4507684141268993, 4507709911072769, 4508457235382273,
        4508972631457793, 4509848804786177, 4511034215759873,
        4511523842031617, 4512838102024193, 4513070030258177,
        4513997743194113, 4514358520446977, 4515260463579137,
        4517090119647233, 4521754454130689, 4525104528621569,
        4526109550968833, 4526856875278337} : Finset ℕ) ⊆
        tzWindow 67108864 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({4504591764815873, 4505983334219777, 4506163722846209,
          4507684141268993, 4507709911072769,
          4508457235382273, 4508972631457793,
          4509848804786177, 4511034215759873,
          4511523842031617, 4512838102024193,
          4513070030258177, 4513997743194113,
          4514358520446977, 4515260463579137,
          4517090119647233, 4521754454130689,
          4525104528621569, 4526109550968833, 4526856875278337} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 67108864 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^27 = 134217728`: window `[18014398509481984, 36028797018963968]` -/

private theorem prime_18014965445165057 : Nat.Prime 18014965445165057 :=
  lucasTwoFactor 1048609 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18018882455339009 : Nat.Prime 18018882455339009 :=
  lucasTwoFactor 1048837 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18026201079611393 : Nat.Prime 18026201079611393 :=
  lucasTwoFactor 1049263 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18029190376849409 : Nat.Prime 18029190376849409 :=
  lucasTwoFactor 1049437 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18033416624668673 : Nat.Prime 18033416624668673 :=
  lucasTwoFactor 1049683 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18038055189348353 : Nat.Prime 18038055189348353 :=
  lucasTwoFactor 1049953 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18039085981499393 : Nat.Prime 18039085981499393 :=
  lucasTwoFactor 1050013 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18044136863039489 : Nat.Prime 18044136863039489 :=
  lucasTwoFactor 1050307 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18055166339055617 : Nat.Prime 18055166339055617 :=
  lucasTwoFactor 1050949 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18056197131206657 : Nat.Prime 18056197131206657 :=
  lucasTwoFactor 1051009 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18058567953154049 : Nat.Prime 18058567953154049 :=
  lucasTwoFactor 1051147 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18064752706060289 : Nat.Prime 18064752706060289 :=
  lucasTwoFactor 1051507 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18070112825245697 : Nat.Prime 18070112825245697 :=
  lucasTwoFactor 1051819 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18090522509836289 : Nat.Prime 18090522509836289 :=
  lucasTwoFactor 1053007 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18091553301987329 : Nat.Prime 18091553301987329 :=
  lucasTwoFactor 1053067 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18098768847044609 : Nat.Prime 18098768847044609 :=
  lucasTwoFactor 1053487 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18100418114486273 : Nat.Prime 18100418114486273 :=
  lucasTwoFactor 1053583 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18102376619573249 : Nat.Prime 18102376619573249 :=
  lucasTwoFactor 1053697 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18107633659543553 : Nat.Prime 18107633659543553 :=
  lucasTwoFactor 1054003 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_18111241432072193 : Nat.Prime 18111241432072193 :=
  lucasTwoFactor 1054213 34 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^27 = 134217728`, `β = 2`.**
The window `[134217728², 2·134217728²] = [18014398509481984, 36028797018963968]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 134217728)`. -/
theorem tzPrimeSupply_134217728_two : TZPrimeSupply 134217728 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((134217728 : ℕ) : ℝ) ^ (2 : ℝ) = 18014398509481984 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (18014965445165057 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18014965445165057, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (18018882455339009 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18018882455339009, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (18026201079611393 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18026201079611393, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (18029190376849409 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18029190376849409, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (18033416624668673 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18033416624668673, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (18038055189348353 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18038055189348353, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (18039085981499393 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18039085981499393, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (18044136863039489 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18044136863039489, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (18055166339055617 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18055166339055617, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (18056197131206657 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18056197131206657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (18058567953154049 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18058567953154049, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (18064752706060289 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18064752706060289, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (18070112825245697 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18070112825245697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (18090522509836289 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18090522509836289, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (18091553301987329 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18091553301987329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (18098768847044609 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18098768847044609, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (18100418114486273 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18100418114486273, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (18102376619573249 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18102376619573249, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (18107633659543553 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18107633659543553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (18111241432072193 : ℕ) ∈ tzWindow 134217728 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_18111241432072193, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({18014965445165057, 18018882455339009, 18026201079611393,
        18029190376849409, 18033416624668673,
        18038055189348353, 18039085981499393,
        18044136863039489, 18055166339055617,
        18056197131206657, 18058567953154049,
        18064752706060289, 18070112825245697,
        18090522509836289, 18091553301987329,
        18098768847044609, 18100418114486273,
        18102376619573249, 18107633659543553,
        18111241432072193} : Finset ℕ) ⊆
        tzWindow 134217728 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({18014965445165057, 18018882455339009, 18026201079611393,
          18029190376849409, 18033416624668673,
          18038055189348353, 18039085981499393,
          18044136863039489, 18055166339055617,
          18056197131206657, 18058567953154049,
          18064752706060289, 18070112825245697,
          18090522509836289, 18091553301987329,
          18098768847044609, 18100418114486273,
          18102376619573249, 18107633659543553,
          18111241432072193} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 134217728 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^28 = 268435456`: window `[72057594037927936, 144115188075855872]` -/

private theorem prime_72071818969612289 : Nat.Prime 72071818969612289 :=
  lucasTwoFactor 1048783 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72093671763214337 : Nat.Prime 72093671763214337 :=
  lucasTwoFactor 1049101 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72096145664376833 : Nat.Prime 72096145664376833 :=
  lucasTwoFactor 1049137 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72129543330070529 : Nat.Prime 72129543330070529 :=
  lucasTwoFactor 1049623 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72139851251580929 : Nat.Prime 72139851251580929 :=
  lucasTwoFactor 1049773 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72143149786464257 : Nat.Prime 72143149786464257 :=
  lucasTwoFactor 1049821 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72180670620762113 : Nat.Prime 72180670620762113 :=
  lucasTwoFactor 1050367 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72211594385293313 : Nat.Prime 72211594385293313 :=
  lucasTwoFactor 1050817 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72256536923078657 : Nat.Prime 72256536923078657 :=
  lucasTwoFactor 1051471 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72289934588772353 : Nat.Prime 72289934588772353 :=
  lucasTwoFactor 1051957 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72298593242841089 : Nat.Prime 72298593242841089 :=
  lucasTwoFactor 1052083 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72325393838768129 : Nat.Prime 72325393838768129 :=
  lucasTwoFactor 1052473 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72386416734109697 : Nat.Prime 72386416734109697 :=
  lucasTwoFactor 1053361 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72409094161432577 : Nat.Prime 72409094161432577 :=
  lucasTwoFactor 1053691 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72452387431776257 : Nat.Prime 72452387431776257 :=
  lucasTwoFactor 1054321 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72466818521890817 : Nat.Prime 72466818521890817 :=
  lucasTwoFactor 1054531 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72492382167236609 : Nat.Prime 72492382167236609 :=
  lucasTwoFactor 1054903 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72515059594559489 : Nat.Prime 72515059594559489 :=
  lucasTwoFactor 1055233 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72516296545140737 : Nat.Prime 72516296545140737 :=
  lucasTwoFactor 1055251 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_72529078367813633 : Nat.Prime 72529078367813633 :=
  lucasTwoFactor 1055437 36 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^28 = 268435456`, `β = 2`.**
The window `[268435456², 2·268435456²] = [72057594037927936, 144115188075855872]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 268435456)`. -/
theorem tzPrimeSupply_268435456_two : TZPrimeSupply 268435456 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((268435456 : ℕ) : ℝ) ^ (2 : ℝ) = 72057594037927936 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (72071818969612289 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72071818969612289, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (72093671763214337 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72093671763214337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (72096145664376833 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72096145664376833, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (72129543330070529 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72129543330070529, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (72139851251580929 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72139851251580929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (72143149786464257 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72143149786464257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (72180670620762113 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72180670620762113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (72211594385293313 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72211594385293313, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (72256536923078657 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72256536923078657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (72289934588772353 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72289934588772353, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (72298593242841089 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72298593242841089, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (72325393838768129 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72325393838768129, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (72386416734109697 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72386416734109697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (72409094161432577 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72409094161432577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (72452387431776257 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72452387431776257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (72466818521890817 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72466818521890817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (72492382167236609 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72492382167236609, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (72515059594559489 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72515059594559489, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (72516296545140737 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72516296545140737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (72529078367813633 : ℕ) ∈ tzWindow 268435456 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_72529078367813633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({72071818969612289, 72093671763214337, 72096145664376833,
        72129543330070529, 72139851251580929,
        72143149786464257, 72180670620762113,
        72211594385293313, 72256536923078657,
        72289934588772353, 72298593242841089,
        72325393838768129, 72386416734109697,
        72409094161432577, 72452387431776257,
        72466818521890817, 72492382167236609,
        72515059594559489, 72516296545140737,
        72529078367813633} : Finset ℕ) ⊆
        tzWindow 268435456 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({72071818969612289, 72093671763214337, 72096145664376833,
          72129543330070529, 72139851251580929,
          72143149786464257, 72180670620762113,
          72211594385293313, 72256536923078657,
          72289934588772353, 72298593242841089,
          72325393838768129, 72386416734109697,
          72409094161432577, 72452387431776257,
          72466818521890817, 72492382167236609,
          72515059594559489, 72516296545140737,
          72529078367813633} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 268435456 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^29 = 536870912`: window `[288230376151711744, 576460752303423488]` -/

private theorem prime_288467046029590529 : Nat.Prime 288467046029590529 :=
  lucasTwoFactor 1049437 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_288575897680740353 : Nat.Prime 288575897680740353 :=
  lucasTwoFactor 1049833 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_288899154099306497 : Nat.Prime 288899154099306497 :=
  lucasTwoFactor 1051009 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_289072327180681217 : Nat.Prime 289072327180681217 :=
  lucasTwoFactor 1051639 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_289121805203931137 : Nat.Prime 289121805203931137 :=
  lucasTwoFactor 1051819 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_289318068029489153 : Nat.Prime 289318068029489153 :=
  lucasTwoFactor 1052533 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290198776843337729 : Nat.Prime 290198776843337729 :=
  lucasTwoFactor 1055737 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290284538750304257 : Nat.Prime 290284538750304257 :=
  lucasTwoFactor 1056049 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290317524099137537 : Nat.Prime 290317524099137537 :=
  lucasTwoFactor 1056169 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290330718238670849 : Nat.Prime 290330718238670849 :=
  lucasTwoFactor 1056217 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290338964575879169 : Nat.Prime 290338964575879169 :=
  lucasTwoFactor 1056247 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290398338203779073 : Nat.Prime 290398338203779073 :=
  lucasTwoFactor 1056463 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290406584540987393 : Nat.Prime 290406584540987393 :=
  lucasTwoFactor 1056493 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290429674285170689 : Nat.Prime 290429674285170689 :=
  lucasTwoFactor 1056577 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290614392238637057 : Nat.Prime 290614392238637057 :=
  lucasTwoFactor 1057249 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290711699017695233 : Nat.Prime 290711699017695233 :=
  lucasTwoFactor 1057603 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290810655064195073 : Nat.Prime 290810655064195073 :=
  lucasTwoFactor 1057963 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290841991145586689 : Nat.Prime 290841991145586689 :=
  lucasTwoFactor 1058077 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290870028692094977 : Nat.Prime 290870028692094977 :=
  lucasTwoFactor 1058179 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_290927753052553217 : Nat.Prime 290927753052553217 :=
  lucasTwoFactor 1058389 38 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^29 = 536870912`, `β = 2`.**
The window `[536870912², 2·536870912²] = [288230376151711744, 576460752303423488]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 536870912)`. -/
theorem tzPrimeSupply_536870912_two : TZPrimeSupply 536870912 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((536870912 : ℕ) : ℝ) ^ (2 : ℝ) = 288230376151711744 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (288467046029590529 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_288467046029590529, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (288575897680740353 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_288575897680740353, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (288899154099306497 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_288899154099306497, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (289072327180681217 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_289072327180681217, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (289121805203931137 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_289121805203931137, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (289318068029489153 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_289318068029489153, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (290198776843337729 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290198776843337729, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (290284538750304257 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290284538750304257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (290317524099137537 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290317524099137537, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (290330718238670849 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290330718238670849, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (290338964575879169 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290338964575879169, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (290398338203779073 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290398338203779073, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (290406584540987393 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290406584540987393, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (290429674285170689 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290429674285170689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (290614392238637057 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290614392238637057, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (290711699017695233 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290711699017695233, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (290810655064195073 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290810655064195073, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (290841991145586689 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290841991145586689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (290870028692094977 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290870028692094977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (290927753052553217 : ℕ) ∈ tzWindow 536870912 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_290927753052553217, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({288467046029590529, 288575897680740353, 288899154099306497,
        289072327180681217, 289121805203931137,
        289318068029489153, 290198776843337729,
        290284538750304257, 290317524099137537,
        290330718238670849, 290338964575879169,
        290398338203779073, 290406584540987393,
        290429674285170689, 290614392238637057,
        290711699017695233, 290810655064195073,
        290841991145586689, 290870028692094977,
        290927753052553217} : Finset ℕ) ⊆
        tzWindow 536870912 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({288467046029590529, 288575897680740353, 288899154099306497,
          289072327180681217, 289121805203931137,
          289318068029489153, 290198776843337729,
          290284538750304257, 290317524099137537,
          290330718238670849, 290338964575879169,
          290398338203779073, 290406584540987393,
          290429674285170689, 290614392238637057,
          290711699017695233, 290810655064195073,
          290841991145586689, 290870028692094977,
          290927753052553217} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 536870912 (2 : ℝ)).card := Finset.card_le_card hsub


end ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/

#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_67108864_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_134217728_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_268435456_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_536870912_two
