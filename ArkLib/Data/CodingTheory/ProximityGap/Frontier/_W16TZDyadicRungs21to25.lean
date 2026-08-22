/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# W16 — intermediate dyadic `TZPrimeSupply` rungs `n = 2^21 .. 2^25` (#466)

Fills the explicit-certificate Thorner–Zaman ladder between the pre-existing top rung
`n = 2^15` (`ThornerZamanInstance.lean`) and the prize-scale rung `n = 2^30`
(`_W16TZPrizeScaleP30.lean`): for each `k = 21..25` this file proves

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

/-! ### Rung `n = 2^21 = 2097152`: window `[4398046511104, 8796093022208]` -/

private theorem prime_4399015395329 : Nat.Prime 4399015395329 :=
  lucasTwoFactor 1048807 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4401557143553 : Nat.Prime 4401557143553 :=
  lucasTwoFactor 1049413 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4403218087937 : Nat.Prime 4403218087937 :=
  lucasTwoFactor 1049809 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4403318751233 : Nat.Prime 4403318751233 :=
  lucasTwoFactor 1049833 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4404602208257 : Nat.Prime 4404602208257 :=
  lucasTwoFactor 1050139 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4405935996929 : Nat.Prime 4405935996929 :=
  lucasTwoFactor 1050457 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4407596941313 : Nat.Prime 4407596941313 :=
  lucasTwoFactor 1050853 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4408251252737 : Nat.Prime 4408251252737 :=
  lucasTwoFactor 1051009 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4408326750209 : Nat.Prime 4408326750209 :=
  lucasTwoFactor 1051027 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4408830066689 : Nat.Prime 4408830066689 :=
  lucasTwoFactor 1051147 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4411346649089 : Nat.Prime 4411346649089 :=
  lucasTwoFactor 1051747 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4412982427649 : Nat.Prime 4412982427649 :=
  lucasTwoFactor 1052137 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4415373180929 : Nat.Prime 4415373180929 :=
  lucasTwoFactor 1052707 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4416933462017 : Nat.Prime 4416933462017 :=
  lucasTwoFactor 1053079 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4419701702657 : Nat.Prime 4419701702657 :=
  lucasTwoFactor 1053739 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4420028858369 : Nat.Prime 4420028858369 :=
  lucasTwoFactor 1053817 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4420934828033 : Nat.Prime 4420934828033 :=
  lucasTwoFactor 1054033 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4421714968577 : Nat.Prime 4421714968577 :=
  lucasTwoFactor 1054219 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4422167953409 : Nat.Prime 4422167953409 :=
  lucasTwoFactor 1054327 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_4422318948353 : Nat.Prime 4422318948353 :=
  lucasTwoFactor 1054363 22 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^21 = 2097152`, `β = 2`.**
The window `[2097152², 2·2097152²] = [4398046511104, 8796093022208]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 2097152)`. -/
theorem tzPrimeSupply_2097152_two : TZPrimeSupply 2097152 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((2097152 : ℕ) : ℝ) ^ (2 : ℝ) = 4398046511104 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (4399015395329 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4399015395329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (4401557143553 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4401557143553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (4403218087937 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4403218087937, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (4403318751233 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4403318751233, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (4404602208257 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4404602208257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (4405935996929 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4405935996929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (4407596941313 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4407596941313, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (4408251252737 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4408251252737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (4408326750209 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4408326750209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (4408830066689 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4408830066689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (4411346649089 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4411346649089, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (4412982427649 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4412982427649, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (4415373180929 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4415373180929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (4416933462017 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4416933462017, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (4419701702657 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4419701702657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (4420028858369 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4420028858369, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (4420934828033 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4420934828033, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (4421714968577 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4421714968577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (4422167953409 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4422167953409, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (4422318948353 : ℕ) ∈ tzWindow 2097152 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_4422318948353, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({4399015395329, 4401557143553, 4403218087937, 4403318751233,
        4404602208257, 4405935996929, 4407596941313,
        4408251252737, 4408326750209, 4408830066689,
        4411346649089, 4412982427649, 4415373180929,
        4416933462017, 4419701702657, 4420028858369,
        4420934828033, 4421714968577, 4422167953409,
        4422318948353} : Finset ℕ) ⊆
        tzWindow 2097152 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({4399015395329, 4401557143553, 4403218087937, 4403318751233,
          4404602208257, 4405935996929, 4407596941313,
          4408251252737, 4408326750209, 4408830066689,
          4411346649089, 4412982427649, 4415373180929,
          4416933462017, 4419701702657, 4420028858369,
          4420934828033, 4421714968577, 4422167953409,
          4422318948353} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 2097152 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^22 = 4194304`: window `[17592186044416, 35184372088832]` -/

private theorem prime_17597571530753 : Nat.Prime 17597571530753 :=
  lucasTwoFactor 1048897 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17599685459969 : Nat.Prime 17599685459969 :=
  lucasTwoFactor 1049023 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17600994082817 : Nat.Prime 17600994082817 :=
  lucasTwoFactor 1049101 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17611161075713 : Nat.Prime 17611161075713 :=
  lucasTwoFactor 1049707 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17613073678337 : Nat.Prime 17613073678337 :=
  lucasTwoFactor 1049821 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17615690924033 : Nat.Prime 17615690924033 :=
  lucasTwoFactor 1049977 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17620120109057 : Nat.Prime 17620120109057 :=
  lucasTwoFactor 1050241 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17621630058497 : Nat.Prime 17621630058497 :=
  lucasTwoFactor 1050331 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17623743987713 : Nat.Prime 17623743987713 :=
  lucasTwoFactor 1050457 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17624851283969 : Nat.Prime 17624851283969 :=
  lucasTwoFactor 1050523 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17631394398209 : Nat.Prime 17631394398209 :=
  lucasTwoFactor 1050913 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17632904347649 : Nat.Prime 17632904347649 :=
  lucasTwoFactor 1051003 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17639950778369 : Nat.Prime 17639950778369 :=
  lucasTwoFactor 1051423 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17653037006849 : Nat.Prime 17653037006849 :=
  lucasTwoFactor 1052203 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17659076804609 : Nat.Prime 17659076804609 :=
  lucasTwoFactor 1052563 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17662499356673 : Nat.Prime 17662499356673 :=
  lucasTwoFactor 1052767 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17663002673153 : Nat.Prime 17663002673153 :=
  lucasTwoFactor 1052797 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17665921908737 : Nat.Prime 17665921908737 :=
  lucasTwoFactor 1052971 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17671458390017 : Nat.Prime 17671458390017 :=
  lucasTwoFactor 1053301 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_17680115433473 : Nat.Prime 17680115433473 :=
  lucasTwoFactor 1053817 24 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^22 = 4194304`, `β = 2`.**
The window `[4194304², 2·4194304²] = [17592186044416, 35184372088832]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 4194304)`. -/
theorem tzPrimeSupply_4194304_two : TZPrimeSupply 4194304 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((4194304 : ℕ) : ℝ) ^ (2 : ℝ) = 17592186044416 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (17597571530753 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17597571530753, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (17599685459969 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17599685459969, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (17600994082817 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17600994082817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (17611161075713 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17611161075713, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (17613073678337 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17613073678337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (17615690924033 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17615690924033, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (17620120109057 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17620120109057, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (17621630058497 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17621630058497, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (17623743987713 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17623743987713, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (17624851283969 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17624851283969, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (17631394398209 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17631394398209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (17632904347649 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17632904347649, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (17639950778369 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17639950778369, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (17653037006849 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17653037006849, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (17659076804609 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17659076804609, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (17662499356673 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17662499356673, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (17663002673153 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17663002673153, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (17665921908737 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17665921908737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (17671458390017 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17671458390017, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (17680115433473 : ℕ) ∈ tzWindow 4194304 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_17680115433473, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({17597571530753, 17599685459969, 17600994082817,
        17611161075713, 17613073678337, 17615690924033,
        17620120109057, 17621630058497, 17623743987713,
        17624851283969, 17631394398209, 17632904347649,
        17639950778369, 17653037006849, 17659076804609,
        17662499356673, 17663002673153, 17665921908737,
        17671458390017, 17680115433473} : Finset ℕ) ⊆
        tzWindow 4194304 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({17597571530753, 17599685459969, 17600994082817,
          17611161075713, 17613073678337, 17615690924033,
          17620120109057, 17621630058497, 17623743987713,
          17624851283969, 17631394398209, 17632904347649,
          17639950778369, 17653037006849, 17659076804609,
          17662499356673, 17663002673153, 17665921908737,
          17671458390017, 17680115433473} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 4194304 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^23 = 8388608`: window `[70368744177664, 140737488355328]` -/

private theorem prime_70449073487873 : Nat.Prime 70449073487873 :=
  lucasTwoFactor 1049773 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70452697366529 : Nat.Prime 70452697366529 :=
  lucasTwoFactor 1049827 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70455113285633 : Nat.Prime 70455113285633 :=
  lucasTwoFactor 1049863 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70461153083393 : Nat.Prime 70461153083393 :=
  lucasTwoFactor 1049953 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70486922887169 : Nat.Prime 70486922887169 :=
  lucasTwoFactor 1050337 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70513095344129 : Nat.Prime 70513095344129 :=
  lucasTwoFactor 1050727 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70515913916417 : Nat.Prime 70515913916417 :=
  lucasTwoFactor 1050769 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70559803113473 : Nat.Prime 70559803113473 :=
  lucasTwoFactor 1051423 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70627851501569 : Nat.Prime 70627851501569 :=
  lucasTwoFactor 1052437 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70630267420673 : Nat.Prime 70630267420673 :=
  lucasTwoFactor 1052473 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70630670073857 : Nat.Prime 70630670073857 :=
  lucasTwoFactor 1052479 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70646776201217 : Nat.Prime 70646776201217 :=
  lucasTwoFactor 1052719 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70670130085889 : Nat.Prime 70670130085889 :=
  lucasTwoFactor 1053067 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70670935392257 : Nat.Prime 70670935392257 :=
  lucasTwoFactor 1053079 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70672143351809 : Nat.Prime 70672143351809 :=
  lucasTwoFactor 1053097 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70704758259713 : Nat.Prime 70704758259713 :=
  lucasTwoFactor 1053583 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70715227242497 : Nat.Prime 70715227242497 :=
  lucasTwoFactor 1053739 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70745426231297 : Nat.Prime 70745426231297 :=
  lucasTwoFactor 1054189 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70753479294977 : Nat.Prime 70753479294977 :=
  lucasTwoFactor 1054309 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_70827567480833 : Nat.Prime 70827567480833 :=
  lucasTwoFactor 1055413 26 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^23 = 8388608`, `β = 2`.**
The window `[8388608², 2·8388608²] = [70368744177664, 140737488355328]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 8388608)`. -/
theorem tzPrimeSupply_8388608_two : TZPrimeSupply 8388608 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((8388608 : ℕ) : ℝ) ^ (2 : ℝ) = 70368744177664 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (70449073487873 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70449073487873, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (70452697366529 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70452697366529, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (70455113285633 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70455113285633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (70461153083393 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70461153083393, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (70486922887169 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70486922887169, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (70513095344129 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70513095344129, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (70515913916417 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70515913916417, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (70559803113473 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70559803113473, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (70627851501569 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70627851501569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (70630267420673 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70630267420673, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (70630670073857 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70630670073857, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (70646776201217 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70646776201217, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (70670130085889 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70670130085889, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (70670935392257 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70670935392257, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (70672143351809 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70672143351809, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (70704758259713 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70704758259713, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (70715227242497 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70715227242497, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (70745426231297 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70745426231297, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (70753479294977 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70753479294977, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (70827567480833 : ℕ) ∈ tzWindow 8388608 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_70827567480833, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({70449073487873, 70452697366529, 70455113285633,
        70461153083393, 70486922887169, 70513095344129,
        70515913916417, 70559803113473, 70627851501569,
        70630267420673, 70630670073857, 70646776201217,
        70670130085889, 70670935392257, 70672143351809,
        70704758259713, 70715227242497, 70745426231297,
        70753479294977, 70827567480833} : Finset ℕ) ⊆
        tzWindow 8388608 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({70449073487873, 70452697366529, 70455113285633,
          70461153083393, 70486922887169, 70513095344129,
          70515913916417, 70559803113473, 70627851501569,
          70630267420673, 70630670073857, 70646776201217,
          70670130085889, 70670935392257, 70672143351809,
          70704758259713, 70715227242497, 70745426231297,
          70753479294977, 70827567480833} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 8388608 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^24 = 16777216`: window `[281474976710656, 562949953421312]` -/

private theorem prime_281625569001473 : Nat.Prime 281625569001473 :=
  lucasTwoFactor 1049137 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_281659391868929 : Nat.Prime 281659391868929 :=
  lucasTwoFactor 1049263 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_281699657187329 : Nat.Prime 281699657187329 :=
  lucasTwoFactor 1049413 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_281722205765633 : Nat.Prime 281722205765633 :=
  lucasTwoFactor 1049497 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_281860718460929 : Nat.Prime 281860718460929 :=
  lucasTwoFactor 1050013 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_281925142970369 : Nat.Prime 281925142970369 :=
  lucasTwoFactor 1050253 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282074929954817 : Nat.Prime 282074929954817 :=
  lucasTwoFactor 1050811 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282076540567553 : Nat.Prime 282076540567553 :=
  lucasTwoFactor 1050817 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282448592109569 : Nat.Prime 282448592109569 :=
  lucasTwoFactor 1052203 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282504963555329 : Nat.Prime 282504963555329 :=
  lucasTwoFactor 1052413 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282735281176577 : Nat.Prime 282735281176577 :=
  lucasTwoFactor 1053271 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282759440367617 : Nat.Prime 282759440367617 :=
  lucasTwoFactor 1053361 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282815811813377 : Nat.Prime 282815811813377 :=
  lucasTwoFactor 1053571 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_282984926150657 : Nat.Prime 282984926150657 :=
  lucasTwoFactor 1054201 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283018749018113 : Nat.Prime 283018749018113 :=
  lucasTwoFactor 1054327 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283036465758209 : Nat.Prime 283036465758209 :=
  lucasTwoFactor 1054393 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283091226591233 : Nat.Prime 283091226591233 :=
  lucasTwoFactor 1054597 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283125049458689 : Nat.Prime 283125049458689 :=
  lucasTwoFactor 1054723 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283179810291713 : Nat.Prime 283179810291713 :=
  lucasTwoFactor 1054927 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_283244234801153 : Nat.Prime 283244234801153 :=
  lucasTwoFactor 1055167 28 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^24 = 16777216`, `β = 2`.**
The window `[16777216², 2·16777216²] = [281474976710656, 562949953421312]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 16777216)`. -/
theorem tzPrimeSupply_16777216_two : TZPrimeSupply 16777216 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((16777216 : ℕ) : ℝ) ^ (2 : ℝ) = 281474976710656 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (281625569001473 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281625569001473, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (281659391868929 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281659391868929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (281699657187329 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281699657187329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (281722205765633 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281722205765633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (281860718460929 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281860718460929, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (281925142970369 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_281925142970369, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (282074929954817 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282074929954817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (282076540567553 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282076540567553, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (282448592109569 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282448592109569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (282504963555329 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282504963555329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (282735281176577 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282735281176577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (282759440367617 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282759440367617, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (282815811813377 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282815811813377, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (282984926150657 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_282984926150657, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (283018749018113 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283018749018113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (283036465758209 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283036465758209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (283091226591233 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283091226591233, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (283125049458689 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283125049458689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (283179810291713 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283179810291713, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (283244234801153 : ℕ) ∈ tzWindow 16777216 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_283244234801153, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({281625569001473, 281659391868929, 281699657187329,
        281722205765633, 281860718460929, 281925142970369,
        282074929954817, 282076540567553, 282448592109569,
        282504963555329, 282735281176577, 282759440367617,
        282815811813377, 282984926150657, 283018749018113,
        283036465758209, 283091226591233, 283125049458689,
        283179810291713, 283244234801153} : Finset ℕ) ⊆
        tzWindow 16777216 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({281625569001473, 281659391868929, 281699657187329,
          281722205765633, 281860718460929, 281925142970369,
          282074929954817, 282076540567553, 282448592109569,
          282504963555329, 282735281176577, 282759440367617,
          282815811813377, 282984926150657, 283018749018113,
          283036465758209, 283091226591233, 283125049458689,
          283179810291713, 283244234801153} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 16777216 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ### Rung `n = 2^25 = 33554432`: window `[1125899906842624, 2251799813685248]` -/

private theorem prime_1126244577968129 : Nat.Prime 1126244577968129 :=
  lucasTwoFactor 1048897 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1126869495709697 : Nat.Prime 1126869495709697 :=
  lucasTwoFactor 1049479 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1126998344728577 : Nat.Prime 1126998344728577 :=
  lucasTwoFactor 1049599 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1127281812570113 : Nat.Prime 1127281812570113 :=
  lucasTwoFactor 1049863 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1127378449334273 : Nat.Prime 1127378449334273 :=
  lucasTwoFactor 1049953 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1127674802077697 : Nat.Prime 1127674802077697 :=
  lucasTwoFactor 1050229 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1127790766194689 : Nat.Prime 1127790766194689 :=
  lucasTwoFactor 1050337 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1128692709326849 : Nat.Prime 1128692709326849 :=
  lucasTwoFactor 1051177 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1131282574606337 : Nat.Prime 1131282574606337 :=
  lucasTwoFactor 1053589 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1131398538723329 : Nat.Prime 1131398538723329 :=
  lucasTwoFactor 1053697 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1131527387742209 : Nat.Prime 1131527387742209 :=
  lucasTwoFactor 1053817 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132010571563009 : Nat.Prime 1132010571563009 :=
  lucasTwoFactor 1054267 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132236057346049 : Nat.Prime 1132236057346049 :=
  lucasTwoFactor 1054477 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132377791266817 : Nat.Prime 1132377791266817 :=
  lucasTwoFactor 1054609 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132815877931009 : Nat.Prime 1132815877931009 :=
  lucasTwoFactor 1055017 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132918957146113 : Nat.Prime 1132918957146113 :=
  lucasTwoFactor 1055113 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1132976939204609 : Nat.Prime 1132976939204609 :=
  lucasTwoFactor 1055167 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1133537432436737 : Nat.Prime 1133537432436737 :=
  lucasTwoFactor 1055689 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1133685608808449 : Nat.Prime 1133685608808449 :=
  lucasTwoFactor 1055827 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1133724263514113 : Nat.Prime 1133724263514113 :=
  lucasTwoFactor 1055863 30 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-- **Concrete discharge of `TZPrimeSupply` for `n = 2^25 = 33554432`, `β = 2`.**
The window `[33554432², 2·33554432²] = [1125899906842624, 2251799813685248]`
contains the twenty Lucas-certified primes above, all `≡ 1 (mod 33554432)`. -/
theorem tzPrimeSupply_33554432_two : TZPrimeSupply 33554432 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((33554432 : ℕ) : ℝ) ^ (2 : ℝ) = 1125899906842624 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (1126244577968129 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1126244577968129, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (1126869495709697 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1126869495709697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (1126998344728577 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1126998344728577, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (1127281812570113 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1127281812570113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (1127378449334273 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1127378449334273, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (1127674802077697 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1127674802077697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (1127790766194689 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1127790766194689, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (1128692709326849 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1128692709326849, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (1131282574606337 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1131282574606337, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (1131398538723329 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1131398538723329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (1131527387742209 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1131527387742209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (1132010571563009 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132010571563009, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (1132236057346049 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132236057346049, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (1132377791266817 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132377791266817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (1132815877931009 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132815877931009, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (1132918957146113 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132918957146113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (1132976939204609 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1132976939204609, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (1133537432436737 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1133537432436737, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (1133685608808449 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1133685608808449, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (1133724263514113 : ℕ) ∈ tzWindow 33554432 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1133724263514113, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub :
      ({1126244577968129, 1126869495709697, 1126998344728577,
        1127281812570113, 1127378449334273, 1127674802077697,
        1127790766194689, 1128692709326849, 1131282574606337,
        1131398538723329, 1131527387742209, 1132010571563009,
        1132236057346049, 1132377791266817, 1132815877931009,
        1132918957146113, 1132976939204609, 1133537432436737,
        1133685608808449, 1133724263514113} : Finset ℕ) ⊆
        tzWindow 33554432 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({1126244577968129, 1126869495709697, 1126998344728577,
          1127281812570113, 1127378449334273,
          1127674802077697, 1127790766194689,
          1128692709326849, 1131282574606337,
          1131398538723329, 1131527387742209,
          1132010571563009, 1132236057346049,
          1132377791266817, 1132815877931009,
          1132918957146113, 1132976939204609,
          1133537432436737, 1133685608808449, 1133724263514113} : Finset ℕ).card := by
        decide
    _ ≤ (tzWindow 33554432 (2 : ℝ)).card := Finset.card_le_card hsub


end ArkLib.ProximityGap.Frontier.W16TZDyadicRungs

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/

#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_2097152_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_4194304_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_8388608_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_16777216_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZDyadicRungs.tzPrimeSupply_33554432_two
