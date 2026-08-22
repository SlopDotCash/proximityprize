/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorLinnikThornerZamanArrow
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-!
# W16 — `TZPrimeSupply` at the literal prize scale `n = 2^30` (#466, thread res:tz-prize-scale)

**Target.** The explicit-certificate Thorner–Zaman ladder (`ThornerZamanInstance.lean`)
discharged the named hypothesis `TZPrimeSupply n β supply` at `β = 2` only through
`n = 32768 = 2^15`.  This file lands the **literal prize-scale rung `n = 2^30`**:

> **`tzPrimeSupply_1073741824_two`** — `TZPrimeSupply 1073741824 (2 : ℝ) 20`:
> the window `[2^60, 2^61]` contains (at least) the twenty explicit primes listed below,
> all `≡ 1 (mod 2^30)`.

**Certificate technology.**  `norm_num`-primality (trial division) is hopeless at sixty bits,
so every window prime is sieved (see `scripts/probes/probe_w16_tz_prize_scale.py`,
deterministic Miller–Rabin below `2^64`) in the two-factor Lucas shape

  `p − 1 = 2^a · c`,  `a = 40`,  `c` an odd prime of ≤ 21 bits,

and certified by Mathlib's `lucas_primality` with witness `g = 3`: three kernel-cheap
modular exponentiations (`g^(p−1) = 1`, `g^((p−1)/2) ≠ 1`, `g^((p−1)/c) ≠ 1`) plus a
`norm_num` primality check on the small cofactor `c`.  `binaryPow` is the locally verified
square-and-multiply exponentiation making the `decide` calls logarithmic in the exponent —
copied verbatim (with provenance) from the landed
`Frontier/_PrizeShapePrimeP30.lean`, which used the same pattern at 158 bits.

**Consumer wiring.**  `TZPrimeSupply` is downward monotone in `supply`
(`tzPrimeSupply_mono`), so this rung feeds every small-supply consumer at `n = 2^30`;
in particular the floor-Linnik arrow (`_FloorLinnikThornerZamanArrow.lean`) turns it into
the now **unconditional** statement `exists_residue_prime_below_prize_scale_two_pow_30`:
a prime `p ≡ 1 (mod 2^30)` with `p ≤ (2^30)^4` exists (indeed `p ≤ 2^61`).

**Honest scope.**  This is a *concrete* discharge at the prize modulus: the asymptotic
[TZ24] form (`ThornerZamanPNTinAP`, supply `~ n^{β−1−o(1)}`) remains the named open
hypothesis.  Moreover the `s = 128` ceiling budget at `n = 2^30` needs
`supply > ≈ 4.9·10^8` at `β = 2` while the whole window `[2^60, 2^61]` only holds
`≈ 5.1·10^7` primes `≡ 1 (mod 2^30)` (heuristically, by the prime-counting density) —
so **no** β = 2 certificate ladder, however long, can feed
`kkh26_mcaDeltaStar_le_of_TZ` at `μ = 7`, `n = 2^30`; that consumer needs `β ≥ 3`.
The probe records the budget-vs-window numbers.
-/

namespace ArkLib.ProximityGap.Frontier.W16TZPrizeScale

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

/-! ## The two-factor Lucas certificate -/

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

/-! ## The twenty explicit window primes (sieved and independently re-verified by
`scripts/probes/probe_w16_tz_prize_scale.py`; each `p = 2^40·c + 1 ∈ [2^60, 2^61]`,
`c` an odd prime, so `p ≡ 1 (mod 2^30)` with room to spare) -/

private theorem prime_1152984176769630209 : Nat.Prime 1152984176769630209 :=
  lucasTwoFactor 1048633 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1153267850769596417 : Nat.Prime 1153267850769596417 :=
  lucasTwoFactor 1048891 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1153676869095129089 : Nat.Prime 1153676869095129089 :=
  lucasTwoFactor 1049263 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1155286554118193153 : Nat.Prime 1155286554118193153 :=
  lucasTwoFactor 1050727 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1155590019327459329 : Nat.Prime 1155590019327459329 :=
  lucasTwoFactor 1051003 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1157305257466789889 : Nat.Prime 1157305257466789889 :=
  lucasTwoFactor 1052563 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1159152437001453569 : Nat.Prime 1159152437001453569 :=
  lucasTwoFactor 1054243 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1159937488303685633 : Nat.Prime 1159937488303685633 :=
  lucasTwoFactor 1054957 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1160392686117584897 : Nat.Prime 1160392686117584897 :=
  lucasTwoFactor 1055371 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1161322872954683393 : Nat.Prime 1161322872954683393 :=
  lucasTwoFactor 1056217 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1161989177001115649 : Nat.Prime 1161989177001115649 :=
  lucasTwoFactor 1056823 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1162767631233581057 : Nat.Prime 1162767631233581057 :=
  lucasTwoFactor 1057531 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1163275605605613569 : Nat.Prime 1163275605605613569 :=
  lucasTwoFactor 1057993 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1163328382163746817 : Nat.Prime 1163328382163746817 :=
  lucasTwoFactor 1058041 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1163935312582279169 : Nat.Prime 1163935312582279169 :=
  lucasTwoFactor 1058593 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1164021074489245697 : Nat.Prime 1164021074489245697 :=
  lucasTwoFactor 1058671 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1164383913326411777 : Nat.Prime 1164383913326411777 :=
  lucasTwoFactor 1059001 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1164456481093844993 : Nat.Prime 1164456481093844993 :=
  lucasTwoFactor 1059067 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1164984246675177473 : Nat.Prime 1164984246675177473 :=
  lucasTwoFactor 1059547 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

private theorem prime_1165149173419343873 : Nat.Prime 1165149173419343873 :=
  lucasTwoFactor 1059697 40 3 (by norm_num) (by norm_num)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)
    (by rw [← binaryPow_eq_pow]; decide)

/-! ## The prize-scale rung -/

/-- **Concrete discharge of `TZPrimeSupply` at the literal prize scale
`n = 2^30 = 1073741824`, `β = 2`.**  The window `[2^60, 2^61] =
`[1152921504606846976, 2305843009213693952]` contains the twenty Lucas-certified primes
above, all `≡ 1 (mod 2^30)`.  Extends the explicit β=2 ladder
(`tzPrimeSupply_{8..32768}_two`, `ThornerZamanInstance.lean`) from `n = 2^15` to the
prize modulus in one step. -/
theorem tzPrimeSupply_1073741824_two : TZPrimeSupply 1073741824 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((1073741824 : ℕ) : ℝ) ^ (2 : ℝ) = 1152921504606846976 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1 : (1152984176769630209 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1152984176769630209, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h2 : (1153267850769596417 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1153267850769596417, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h3 : (1153676869095129089 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1153676869095129089, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h4 : (1155286554118193153 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1155286554118193153, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h5 : (1155590019327459329 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1155590019327459329, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h6 : (1157305257466789889 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1157305257466789889, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h7 : (1159152437001453569 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1159152437001453569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h8 : (1159937488303685633 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1159937488303685633, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h9 : (1160392686117584897 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1160392686117584897, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h10 : (1161322872954683393 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1161322872954683393, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h11 : (1161989177001115649 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1161989177001115649, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h12 : (1162767631233581057 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1162767631233581057, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h13 : (1163275605605613569 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1163275605605613569, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h14 : (1163328382163746817 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1163328382163746817, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h15 : (1163935312582279169 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1163935312582279169, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h16 : (1164021074489245697 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1164021074489245697, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h17 : (1164383913326411777 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1164383913326411777, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h18 : (1164456481093844993 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1164456481093844993, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h19 : (1164984246675177473 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1164984246675177473, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have h20 : (1165149173419343873 : ℕ) ∈ tzWindow 1073741824 (2 : ℝ) := by
    rw [mem_tzWindow]
    exact ⟨prime_1165149173419343873, by decide, by rw [hpow]; norm_num,
      by rw [hpow]; norm_num⟩
  have hsub : ({1152984176769630209, 1153267850769596417, 1153676869095129089,
      1155286554118193153, 1155590019327459329, 1157305257466789889, 1159152437001453569,
      1159937488303685633, 1160392686117584897, 1161322872954683393, 1161989177001115649,
      1162767631233581057, 1163275605605613569, 1163328382163746817, 1163935312582279169,
      1164021074489245697, 1164383913326411777, 1164456481093844993, 1164984246675177473,
      1165149173419343873} : Finset ℕ) ⊆ tzWindow 1073741824 (2 : ℝ) := by
    intro p hp
    fin_cases hp <;> assumption
  calc (20 : ℕ)
      = ({1152984176769630209, 1153267850769596417, 1153676869095129089,
      1155286554118193153, 1155590019327459329, 1157305257466789889, 1159152437001453569,
      1159937488303685633, 1160392686117584897, 1161322872954683393, 1161989177001115649,
      1162767631233581057, 1163275605605613569, 1163328382163746817, 1163935312582279169,
      1164021074489245697, 1164383913326411777, 1164456481093844993, 1164984246675177473,
      1165149173419343873} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1073741824 (2 : ℝ)).card := Finset.card_le_card hsub

/-! ## Consumer wiring -/

/-- `TZPrimeSupply` is downward monotone in the supply count (pure unpacking). -/
theorem tzPrimeSupply_mono {n : ℕ} {β : ℝ} {s s' : ℕ} (h : s' ≤ s)
    (hTZ : TZPrimeSupply n β s) : TZPrimeSupply n β s' :=
  ⟨h.trans hTZ.le_card⟩

/-- The prize-scale rung in `2^30` power form. -/
theorem tzPrimeSupply_two_pow_30_two : TZPrimeSupply (2 ^ 30) (2 : ℝ) 20 := by
  have h : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  rw [h]
  exact tzPrimeSupply_1073741824_two

/-- **Unconditional floor-Linnik delivery at the prize modulus:** a prime
`p ≡ 1 (mod 2^30)` below prize scale `(2^30)^4` exists — the previously conditional
consumer `tzSupplyOne_gives_residue_prime_below_prize` fires on the explicit rung
(with `β = 2 ≤ 3`, supply `20 ≥ 1`). -/
theorem exists_residue_prime_below_prize_scale_two_pow_30 :
    ∃ p : ℕ, p.Prime ∧ p % 2 ^ 30 = 1 ∧ (p : ℝ) ≤ ((2 ^ 30 : ℕ) : ℝ) ^ 4 :=
  ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow.tzSupplyOne_gives_residue_prime_below_prize
    (by norm_num) (by norm_num)
    (tzPrimeSupply_mono (by norm_num) tzPrimeSupply_two_pow_30_two)

end ArkLib.ProximityGap.Frontier.W16TZPrizeScale

/-! ## Axiom audit (must show ONLY [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.Frontier.W16TZPrizeScale.tzPrimeSupply_1073741824_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZPrizeScale.tzPrimeSupply_two_pow_30_two
#print axioms ArkLib.ProximityGap.Frontier.W16TZPrizeScale.tzPrimeSupply_mono
#print axioms
  ArkLib.ProximityGap.Frontier.W16TZPrizeScale.exists_residue_prime_below_prize_scale_two_pow_30
