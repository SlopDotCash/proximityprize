/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Concrete four-rate numeric certificate for the ABF26 §1 MCA prize (issue #120)

The apex `mcaPrize` deliverable (`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`)
asks to resolve the Grand MCA Challenge at every prize rate `ρ ∈ {1/2, 1/4, 1/8, 1/16}` with
`ε* = 2^(-128)`.  The packaged route `mcaPrize_of_large_field` /
`mcaPrize_resolutions_of_large_field` reduces this, at a fixed evaluation-domain size `|L| = n`,
to two purely numeric side conditions per rate `j` (writing `kⱼ := ⌊ρⱼ · n⌋`):

* the **large-field separation** `C(C(n, kⱼ+1), 2) < |F|` (from `epsMCA_one_eq_choose_div`);
* the **counting bound** `C(n, kⱼ+1) / |F| ≤ ε*`.

This file supplies that numeric substrate **concretely at `n = 16`** together with a concrete
carrier field, all in a mathlib-only import cone (no proximity dependencies), so it verifies
independently of the (currently churning) ArkLib root build.  The complementary assembly that
plugs these into `mcaPrize_of_large_field` lives in the ProximityGap layer (issue #120), and
the `ENNReal → ℕ` reduction bridge `epsStar_bound_of_nat` is tracked separately.

## Key choices

* `prizeRates j = 1 / 2^(j+1)`, so at `|L| = 16` the four `kⱼ + 1` are `{9, 5, 3, 2}` and the
  binomials `C(16, kⱼ+1)` are `{11440, 4368, 560, 120}` (max `11440`).
* The counting bound at `ε* = 2^(-128)` reduces to `C(16, kⱼ+1) ≤ 2^14 = 16384`, which the
  max `11440` satisfies.
* **Carrier:** `GaloisField 2 142`, of cardinality `2^142 = 2^14 · 2^128`.  Using a Galois
  field of prime-power order sidesteps any large-prime primality certificate: `2^142` exceeds
  both `2^128 · 11440` (counting bound) and `C(11440, 2) = 65431080` (separation), so all four
  rates clear simultaneously.

`#print axioms` for every result below is `[propext, Classical.choice, Quot.sound]`.
-/

open scoped NNReal ENNReal

namespace MCAPrizeFourRateNumerics

/-- `Fact (Nat.Prime 2)`, needed to form the carrier `GaloisField 2 142`.  ArkLib otherwise
carries `Fact (Nat.Prime p)` only as a section variable, so no global instance pre-exists; this
one is harmless (it concerns the concrete prime `2`). -/
instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Floor evaluations: `⌊prizeRates j · 16⌋₊`

With `prizeRates j = 1 / 2^(j+1)` and `|L| = 16`, these give `kⱼ ∈ {8, 4, 2, 1}`.  Stated on
the explicit `ℝ≥0` expression so they rewrite after `unfold prizeRates` + `Fintype.card_fin`. -/

/-- Rate `ρ₀ = 1/2`: `⌊(1/2) · 16⌋₊ = 8`. -/
lemma floor_rate0 : ⌊(1 / 2 ^ (0 + 1) : ℝ≥0) * 16⌋₊ = 8 := by norm_num

/-- Rate `ρ₁ = 1/4`: `⌊(1/4) · 16⌋₊ = 4`. -/
lemma floor_rate1 : ⌊(1 / 2 ^ (1 + 1) : ℝ≥0) * 16⌋₊ = 4 := by norm_num

/-- Rate `ρ₂ = 1/8`: `⌊(1/8) · 16⌋₊ = 2`. -/
lemma floor_rate2 : ⌊(1 / 2 ^ (2 + 1) : ℝ≥0) * 16⌋₊ = 2 := by norm_num

/-- Rate `ρ₃ = 1/16`: `⌊(1/16) · 16⌋₊ = 1`. -/
lemma floor_rate3 : ⌊(1 / 2 ^ (3 + 1) : ℝ≥0) * 16⌋₊ = 1 := by norm_num

/-! ## Binomial evaluations: `C(16, kⱼ+1)` at the four rates. -/

lemma choose16_9 : Nat.choose 16 9 = 11440 := by decide
lemma choose16_5 : Nat.choose 16 5 = 4368 := by decide
lemma choose16_3 : Nat.choose 16 3 = 560 := by decide
lemma choose16_2 : Nat.choose 16 2 = 120 := by decide

/-! ## Large-field separation: `C(C(16, kⱼ+1), 2) < 2^142`

This is the strict separation `epsMCA_one_eq_choose_div` requires (`C(C(n,k+1),2) < |F|`). -/

lemma separation_rate0 : Nat.choose (Nat.choose 16 9) 2 < 2 ^ 142 := by
  rw [choose16_9, Nat.choose_two_right]; norm_num

lemma separation_rate1 : Nat.choose (Nat.choose 16 5) 2 < 2 ^ 142 := by
  rw [choose16_5, Nat.choose_two_right]; norm_num

lemma separation_rate2 : Nat.choose (Nat.choose 16 3) 2 < 2 ^ 142 := by
  rw [choose16_3, Nat.choose_two_right]; norm_num

lemma separation_rate3 : Nat.choose (Nat.choose 16 2) 2 < 2 ^ 142 := by
  rw [choose16_2, Nat.choose_two_right]; norm_num

/-! ## Counting bound, `ℕ` form: `C(16, kⱼ+1) · 2^128 ≤ 2^142`

This is the `ε* = 2^(-128)` counting bound cleared of `ENNReal` division (the shape produced
by the `epsStar_bound_of_nat` bridge): `C(n,k+1)/|F| ≤ 2^(-128) ⇔ 2^128 · C(n,k+1) ≤ |F|`. -/

lemma counting_nat_rate0 : Nat.choose 16 9 * 2 ^ 128 ≤ 2 ^ 142 := by rw [choose16_9]; norm_num
lemma counting_nat_rate1 : Nat.choose 16 5 * 2 ^ 128 ≤ 2 ^ 142 := by rw [choose16_5]; norm_num
lemma counting_nat_rate2 : Nat.choose 16 3 * 2 ^ 128 ≤ 2 ^ 142 := by rw [choose16_3]; norm_num
lemma counting_nat_rate3 : Nat.choose 16 2 * 2 ^ 128 ≤ 2 ^ 142 := by rw [choose16_2]; norm_num

/-! ## Counting bound, `ENNReal` form: `C(16, kⱼ+1) / 2^142 ≤ (2^128)⁻¹`

The exact shape `mcaPrize_of_large_field`'s `hbound` consumes once `|F| = 2^142` and
`(ε* : ℝ≥0∞) = (2^128)⁻¹` (see `epsStar_coe_eq_inv`). -/

/-- Reusable core: `(c : ℝ≥0∞) / 2^142 ≤ (2^128)⁻¹` whenever `c ≤ 2^14`. -/
lemma enn_count_of_le (c : ℕ) (hc : c ≤ 2 ^ 14) :
    (c : ℝ≥0∞) / 2 ^ 142 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by simp))]
  have h142 : (2 : ℝ≥0∞) ^ 142 = 2 ^ 128 * 2 ^ 14 := by rw [← pow_add]
  rw [h142, ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), one_mul]
  exact_mod_cast hc

lemma counting_enn_rate0 : (Nat.choose 16 9 : ℝ≥0∞) / 2 ^ 142 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  enn_count_of_le _ (by rw [choose16_9]; norm_num)
lemma counting_enn_rate1 : (Nat.choose 16 5 : ℝ≥0∞) / 2 ^ 142 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  enn_count_of_le _ (by rw [choose16_5]; norm_num)
lemma counting_enn_rate2 : (Nat.choose 16 3 : ℝ≥0∞) / 2 ^ 142 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  enn_count_of_le _ (by rw [choose16_3]; norm_num)
lemma counting_enn_rate3 : (Nat.choose 16 2 : ℝ≥0∞) / 2 ^ 142 ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ :=
  enn_count_of_le _ (by rw [choose16_2]; norm_num)

/-- `(ε* : ℝ≥0∞) = (2^128)⁻¹` where `ε* = 1 / 2^128 : ℝ≥0`.  Lets the `counting_enn_*` bounds
be read directly against the cast of the in-tree `epsStar`. -/
lemma epsStar_coe_eq_inv : ((1 / 2 ^ 128 : ℝ≥0) : ℝ≥0∞) = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [one_div, ENNReal.coe_inv (by positivity), ENNReal.coe_pow, ENNReal.coe_ofNat]

/-! ## Concrete carrier: `GaloisField 2 142`

Using a Galois field of prime-power order `2^142` sidesteps any large-prime primality
certificate.  `GaloisField p n` is `Finite` (not `Fintype` by default), so its size is stated
via `Nat.card`; an assembly that needs `Fintype.card F` obtains the `Fintype` from
`Fintype.ofFinite` and bridges with `Nat.card_eq_fintype_card`. -/

/-- The carrier field has cardinality `2^142`, exceeding both `2^128 · 11440` (counting bound)
and `C(11440, 2) = 65431080` (separation), so all four prize-rate side conditions clear
simultaneously — with no primality certificate required. -/
lemma natCard_galoisField : Nat.card (GaloisField 2 142) = 2 ^ 142 :=
  GaloisField.card 2 142 (by norm_num)

end MCAPrizeFourRateNumerics

-- Axiom audit (issue #120): every result is kernel-clean.
#print axioms MCAPrizeFourRateNumerics.floor_rate0
#print axioms MCAPrizeFourRateNumerics.separation_rate0
#print axioms MCAPrizeFourRateNumerics.counting_nat_rate0
#print axioms MCAPrizeFourRateNumerics.counting_enn_rate0
#print axioms MCAPrizeFourRateNumerics.epsStar_coe_eq_inv
#print axioms MCAPrizeFourRateNumerics.natCard_galoisField
