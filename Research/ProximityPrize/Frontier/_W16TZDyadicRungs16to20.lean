/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# W16 — intermediate dyadic `TZPrimeSupply` rungs `n = 2^16 .. 2^20` (#466)

Fills the explicit-certificate Thorner–Zaman ladder between the pre-existing top rung
`n = 2^15` (`ThornerZamanInstance.lean`) and the prize-scale rung `n = 2^30`
(`_W16TZPrizeScaleP30.lean`): for each `k = 16..20` this file proves

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

/-! ### Rung `n = 2^16 = 65536`: window `[4294967296, 8589934592]` -/

private theorem prime_4298309633 : Nat.Prime 4298309633 :=
  lucasTwoFactor 65587 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4332126209 : Nat.Prime 4332126209 :=
  lucasTwoFactor 66103 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4355719169 : Nat.Prime 4355719169 :=
  lucasTwoFactor 66463 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4387176449 : Nat.Prime 4387176449 :=
  lucasTwoFactor 66943 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4394647553 : Nat.Prime 4394647553 :=
  lucasTwoFactor 67057 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4400152577 : Nat.Prime 4400152577 :=
  lucasTwoFactor 67141 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4400939009 : Nat.Prime 4400939009 :=
  lucasTwoFactor 67153 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4442226689 : Nat.Prime 4442226689 :=
  lucasTwoFactor 67783 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4443406337 : Nat.Prime 4443406337 :=
  lucasTwoFactor 67801 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4457955329 : Nat.Prime 4457955329 :=
  lucasTwoFactor 68023 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4459921409 : Nat.Prime 4459921409 :=
  lucasTwoFactor 68053 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4476829697 : Nat.Prime 4476829697 :=
  lucasTwoFactor 68311 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4490592257 : Nat.Prime 4490592257 :=
  lucasTwoFactor 68521 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4513005569 : Nat.Prime 4513005569 :=
  lucasTwoFactor 68863 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4514185217 : Nat.Prime 4514185217 :=
  lucasTwoFactor 68881 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4542496769 : Nat.Prime 4542496769 :=
  lucasTwoFactor 69313 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4544069633 : Nat.Prime 4544069633 :=
  lucasTwoFactor 69337 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4565303297 : Nat.Prime 4565303297 :=
  lucasTwoFactor 69661 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4595187713 : Nat.Prime 4595187713 :=
  lucasTwoFactor 70117 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4595580929 : Nat.Prime 4595580929 :=
  lucasTwoFactor 70123 16 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^16 = 65536`, `β = 2`.**
The window `[65536², 2·65536²] = [4294967296, 8589934592]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 65536)`. -/
theorem tzPrimeSupply_65536_two : TZPrimeSupply 65536 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((65536 : ℕ) : ℝ) ^ (2 : ℝ) = 4294967296 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (4298309633 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4298309633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (4332126209 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4332126209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (4355719169 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4355719169, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (4387176449 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4387176449, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (4394647553 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4394647553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (4400152577 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4400152577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (4400939009 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4400939009, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (4442226689 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4442226689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (4443406337 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4443406337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (4457955329 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4457955329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (4459921409 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4459921409, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (4476829697 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4476829697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (4490592257 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4490592257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (4513005569 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4513005569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (4514185217 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4514185217, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (4542496769 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4542496769, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (4544069633 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4544069633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (4565303297 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4565303297, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (4595187713 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4595187713, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (4595580929 : ℕ) ∈ tzWindow 65536 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4595580929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({4298309633, 4332126209, 4355719169, 4387176449, 4394647553,
        4400152577, 4400939009, 4442226689, 4443406337,
        4457955329, 4459921409, 4476829697, 4490592257,
        4513005569, 4514185217, 4542496769, 4544069633,
        4565303297, 4595187713, 4595580929} : Finset ℕ) ⊆
        tzWindow 65536 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({4298309633, 4332126209, 4355719169, 4387176449, 4394647553,
          4400152577, 4400939009, 4442226689, 4443406337,
          4457955329, 4459921409, 4476829697, 4490592257,
          4513005569, 4514185217, 4542496769, 4544069633,
          4565303297, 4595187713, 4595580929} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 65536 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^17 = 131072`: window `[17179869184, 34359738368]` -/

private theorem prime_17203068929 : Nat.Prime 17203068929 :=
  lucasTwoFactor 131249 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17210146817 : Nat.Prime 17210146817 :=
  lucasTwoFactor 131303 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17287217153 : Nat.Prime 17287217153 :=
  lucasTwoFactor 131891 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17309237249 : Nat.Prime 17309237249 :=
  lucasTwoFactor 132059 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17310810113 : Nat.Prime 17310810113 :=
  lucasTwoFactor 132071 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17381588993 : Nat.Prime 17381588993 :=
  lucasTwoFactor 132611 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17391812609 : Nat.Prime 17391812609 :=
  lucasTwoFactor 132689 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17410686977 : Nat.Prime 17410686977 :=
  lucasTwoFactor 132833 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17420910593 : Nat.Prime 17420910593 :=
  lucasTwoFactor 132911 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17478320129 : Nat.Prime 17478320129 :=
  lucasTwoFactor 133349 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17485398017 : Nat.Prime 17485398017 :=
  lucasTwoFactor 133403 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17491689473 : Nat.Prime 17491689473 :=
  lucasTwoFactor 133451 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17497194497 : Nat.Prime 17497194497 :=
  lucasTwoFactor 133493 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17508990977 : Nat.Prime 17508990977 :=
  lucasTwoFactor 133583 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17525506049 : Nat.Prime 17525506049 :=
  lucasTwoFactor 133709 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17533370369 : Nat.Prime 17533370369 :=
  lucasTwoFactor 133769 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17586061313 : Nat.Prime 17586061313 :=
  lucasTwoFactor 134171 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17591566337 : Nat.Prime 17591566337 :=
  lucasTwoFactor 134213 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17595498497 : Nat.Prime 17595498497 :=
  lucasTwoFactor 134243 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17698521089 : Nat.Prime 17698521089 :=
  lucasTwoFactor 135029 17 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^17 = 131072`, `β = 2`.**
The window `[131072², 2·131072²] = [17179869184, 34359738368]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 131072)`. -/
theorem tzPrimeSupply_131072_two : TZPrimeSupply 131072 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((131072 : ℕ) : ℝ) ^ (2 : ℝ) = 17179869184 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (17203068929 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17203068929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (17210146817 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17210146817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (17287217153 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17287217153, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (17309237249 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17309237249, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (17310810113 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17310810113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (17381588993 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17381588993, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (17391812609 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17391812609, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (17410686977 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17410686977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (17420910593 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17420910593, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (17478320129 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17478320129, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (17485398017 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17485398017, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (17491689473 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17491689473, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (17497194497 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17497194497, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (17508990977 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17508990977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (17525506049 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17525506049, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (17533370369 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17533370369, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (17586061313 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17586061313, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (17591566337 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17591566337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (17595498497 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17595498497, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (17698521089 : ℕ) ∈ tzWindow 131072 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17698521089, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({17203068929, 17210146817, 17287217153, 17309237249,
        17310810113, 17381588993, 17391812609, 17410686977,
        17420910593, 17478320129, 17485398017, 17491689473,
        17497194497, 17508990977, 17525506049, 17533370369,
        17586061313, 17591566337, 17595498497, 17698521089} : Finset ℕ) ⊆
        tzWindow 131072 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({17203068929, 17210146817, 17287217153, 17309237249,
          17310810113, 17381588993, 17391812609, 17410686977,
          17420910593, 17478320129, 17485398017, 17491689473,
          17497194497, 17508990977, 17525506049, 17533370369,
          17586061313, 17591566337, 17595498497, 17698521089} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 131072 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^18 = 262144`: window `[68719476736, 137438953472]` -/

private theorem prime_68877549569 : Nat.Prime 68877549569 :=
  lucasTwoFactor 262747 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68975067137 : Nat.Prime 68975067137 :=
  lucasTwoFactor 263119 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_68998660097 : Nat.Prime 68998660097 :=
  lucasTwoFactor 263209 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69006524417 : Nat.Prime 69006524417 :=
  lucasTwoFactor 263239 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69083594753 : Nat.Prime 69083594753 :=
  lucasTwoFactor 263533 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69280202753 : Nat.Prime 69280202753 :=
  lucasTwoFactor 264283 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69407604737 : Nat.Prime 69407604737 :=
  lucasTwoFactor 264769 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69468946433 : Nat.Prime 69468946433 :=
  lucasTwoFactor 265003 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69555453953 : Nat.Prime 69555453953 :=
  lucasTwoFactor 265333 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69557026817 : Nat.Prime 69557026817 :=
  lucasTwoFactor 265339 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69577474049 : Nat.Prime 69577474049 :=
  lucasTwoFactor 265417 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69579046913 : Nat.Prime 69579046913 :=
  lucasTwoFactor 265423 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69822840833 : Nat.Prime 69822840833 :=
  lucasTwoFactor 266353 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69907775489 : Nat.Prime 69907775489 :=
  lucasTwoFactor 266677 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_69931368449 : Nat.Prime 69931368449 :=
  lucasTwoFactor 266767 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70017875969 : Nat.Prime 70017875969 :=
  lucasTwoFactor 267097 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70041468929 : Nat.Prime 70041468929 :=
  lucasTwoFactor 267187 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70044614657 : Nat.Prime 70044614657 :=
  lucasTwoFactor 267199 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70098092033 : Nat.Prime 70098092033 :=
  lucasTwoFactor 267403 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70129549313 : Nat.Prime 70129549313 :=
  lucasTwoFactor 267523 18 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^18 = 262144`, `β = 2`.**
The window `[262144², 2·262144²] = [68719476736, 137438953472]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 262144)`. -/
theorem tzPrimeSupply_262144_two : TZPrimeSupply 262144 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((262144 : ℕ) : ℝ) ^ (2 : ℝ) = 68719476736 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (68877549569 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68877549569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (68975067137 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68975067137, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (68998660097 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_68998660097, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (69006524417 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69006524417, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (69083594753 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69083594753, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (69280202753 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69280202753, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (69407604737 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69407604737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (69468946433 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69468946433, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (69555453953 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69555453953, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (69557026817 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69557026817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (69577474049 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69577474049, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (69579046913 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69579046913, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (69822840833 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69822840833, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (69907775489 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69907775489, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (69931368449 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_69931368449, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (70017875969 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70017875969, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (70041468929 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70041468929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (70044614657 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70044614657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (70098092033 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70098092033, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (70129549313 : ℕ) ∈ tzWindow 262144 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70129549313, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({68877549569, 68975067137, 68998660097, 69006524417,
        69083594753, 69280202753, 69407604737, 69468946433,
        69555453953, 69557026817, 69577474049, 69579046913,
        69822840833, 69907775489, 69931368449, 70017875969,
        70041468929, 70044614657, 70098092033, 70129549313} : Finset ℕ) ⊆
        tzWindow 262144 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({68877549569, 68975067137, 68998660097, 69006524417,
          69083594753, 69280202753, 69407604737, 69468946433,
          69555453953, 69557026817, 69577474049, 69579046913,
          69822840833, 69907775489, 69931368449, 70017875969,
          70041468929, 70044614657, 70098092033, 70129549313} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 262144 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^19 = 524288`: window `[274877906944, 549755813888]` -/

private theorem prime_275162595329 : Nat.Prime 275162595329 :=
  lucasTwoFactor 524831 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_275234947073 : Nat.Prime 275234947073 :=
  lucasTwoFactor 524969 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_275448856577 : Nat.Prime 275448856577 :=
  lucasTwoFactor 525377 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_275602997249 : Nat.Prime 275602997249 :=
  lucasTwoFactor 525671 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_275838926849 : Nat.Prime 275838926849 :=
  lucasTwoFactor 526121 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_276043399169 : Nat.Prime 276043399169 :=
  lucasTwoFactor 526511 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_276115750913 : Nat.Prime 276115750913 :=
  lucasTwoFactor 526649 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_276210122753 : Nat.Prime 276210122753 :=
  lucasTwoFactor 526829 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_276776353793 : Nat.Prime 276776353793 :=
  lucasTwoFactor 527909 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277311127553 : Nat.Prime 277311127553 :=
  lucasTwoFactor 528929 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277443248129 : Nat.Prime 277443248129 :=
  lucasTwoFactor 529181 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277635137537 : Nat.Prime 277635137537 :=
  lucasTwoFactor 529547 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277805006849 : Nat.Prime 277805006849 :=
  lucasTwoFactor 529871 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277852192769 : Nat.Prime 277852192769 :=
  lucasTwoFactor 529961 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277899378689 : Nat.Prime 277899378689 :=
  lucasTwoFactor 530051 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_277965438977 : Nat.Prime 277965438977 :=
  lucasTwoFactor 530177 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_278106996737 : Nat.Prime 278106996737 :=
  lucasTwoFactor 530447 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_278185639937 : Nat.Prime 278185639937 :=
  lucasTwoFactor 530597 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_278223388673 : Nat.Prime 278223388673 :=
  lucasTwoFactor 530669 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_278311469057 : Nat.Prime 278311469057 :=
  lucasTwoFactor 530837 19 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^19 = 524288`, `β = 2`.**
The window `[524288², 2·524288²] = [274877906944, 549755813888]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 524288)`. -/
theorem tzPrimeSupply_524288_two : TZPrimeSupply 524288 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((524288 : ℕ) : ℝ) ^ (2 : ℝ) = 274877906944 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (275162595329 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_275162595329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (275234947073 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_275234947073, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (275448856577 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_275448856577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (275602997249 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_275602997249, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (275838926849 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_275838926849, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (276043399169 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_276043399169, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (276115750913 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_276115750913, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (276210122753 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_276210122753, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (276776353793 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_276776353793, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (277311127553 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277311127553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (277443248129 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277443248129, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (277635137537 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277635137537, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (277805006849 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277805006849, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (277852192769 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277852192769, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (277899378689 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277899378689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (277965438977 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_277965438977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (278106996737 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_278106996737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (278185639937 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_278185639937, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (278223388673 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_278223388673, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (278311469057 : ℕ) ∈ tzWindow 524288 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_278311469057, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({275162595329, 275234947073, 275448856577, 275602997249,
        275838926849, 276043399169, 276115750913,
        276210122753, 276776353793, 277311127553,
        277443248129, 277635137537, 277805006849,
        277852192769, 277899378689, 277965438977,
        278106996737, 278185639937, 278223388673, 278311469057} : Finset ℕ) ⊆
        tzWindow 524288 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({275162595329, 275234947073, 275448856577, 275602997249,
          275838926849, 276043399169, 276115750913,
          276210122753, 276776353793, 277311127553,
          277443248129, 277635137537, 277805006849,
          277852192769, 277899378689, 277965438977,
          278106996737, 278185639937, 278223388673,
          278311469057} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 524288 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^20 = 1048576`: window `[1099511627776, 2199023255552]` -/

private theorem prime_1100036964353 : Nat.Prime 1100036964353 :=
  lucasTwoFactor 1049077 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1100093587457 : Nat.Prime 1100093587457 :=
  lucasTwoFactor 1049131 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1100508823553 : Nat.Prime 1100508823553 :=
  lucasTwoFactor 1049527 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1100829687809 : Nat.Prime 1100829687809 :=
  lucasTwoFactor 1049833 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1101163134977 : Nat.Prime 1101163134977 :=
  lucasTwoFactor 1050151 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1101351878657 : Nat.Prime 1101351878657 :=
  lucasTwoFactor 1050331 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1101477707777 : Nat.Prime 1101477707777 :=
  lucasTwoFactor 1050451 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1102673084417 : Nat.Prime 1102673084417 :=
  lucasTwoFactor 1051591 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1103906209793 : Nat.Prime 1103906209793 :=
  lucasTwoFactor 1052767 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1104340320257 : Nat.Prime 1104340320257 :=
  lucasTwoFactor 1053181 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1104466149377 : Nat.Prime 1104466149377 :=
  lucasTwoFactor 1053301 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1104661184513 : Nat.Prime 1104661184513 :=
  lucasTwoFactor 1053487 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1105007214593 : Nat.Prime 1105007214593 :=
  lucasTwoFactor 1053817 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1105535696897 : Nat.Prime 1105535696897 :=
  lucasTwoFactor 1054321 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1105661526017 : Nat.Prime 1105661526017 :=
  lucasTwoFactor 1054441 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1105850269697 : Nat.Prime 1105850269697 :=
  lucasTwoFactor 1054621 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1107140018177 : Nat.Prime 1107140018177 :=
  lucasTwoFactor 1055851 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1107171475457 : Nat.Prime 1107171475457 :=
  lucasTwoFactor 1055881 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1107184058369 : Nat.Prime 1107184058369 :=
  lucasTwoFactor 1055893 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1107360219137 : Nat.Prime 1107360219137 :=
  lucasTwoFactor 1056061 20 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^20 = 1048576`, `β = 2`.**
The window `[1048576², 2·1048576²] = [1099511627776, 2199023255552]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 1048576)`. -/
theorem tzPrimeSupply_1048576_two : TZPrimeSupply 1048576 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((1048576 : ℕ) : ℝ) ^ (2 : ℝ) = 1099511627776 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (1100036964353 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1100036964353, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (1100093587457 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1100093587457, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (1100508823553 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1100508823553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (1100829687809 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1100829687809, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (1101163134977 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1101163134977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (1101351878657 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1101351878657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (1101477707777 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1101477707777, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (1102673084417 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1102673084417, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (1103906209793 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1103906209793, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (1104340320257 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1104340320257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (1104466149377 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1104466149377, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (1104661184513 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1104661184513, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (1105007214593 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1105007214593, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (1105535696897 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1105535696897, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (1105661526017 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1105661526017, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (1105850269697 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1105850269697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (1107140018177 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1107140018177, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (1107171475457 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1107171475457, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (1107184058369 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1107184058369, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (1107360219137 : ℕ) ∈ tzWindow 1048576 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1107360219137, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({1100036964353, 1100093587457, 1100508823553, 1100829687809,
        1101163134977, 1101351878657, 1101477707777,
        1102673084417, 1103906209793, 1104340320257,
        1104466149377, 1104661184513, 1105007214593,
        1105535696897, 1105661526017, 1105850269697,
        1107140018177, 1107171475457, 1107184058369,
        1107360219137} : Finset ℕ) ⊆
        tzWindow 1048576 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({1100036964353, 1100093587457, 1100508823553, 1100829687809,
          1101163134977, 1101351878657, 1101477707777,
          1102673084417, 1103906209793, 1104340320257,
          1104466149377, 1104661184513, 1105007214593,
          1105535696897, 1105661526017, 1105850269697,
          1107140018177, 1107171475457, 1107184058369,
          1107360219137} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 1048576 (2 : ℝ)).card := Finset.card_le_card hsub


end ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/

#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_65536_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_131072_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_262144_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_524288_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_1048576_two
