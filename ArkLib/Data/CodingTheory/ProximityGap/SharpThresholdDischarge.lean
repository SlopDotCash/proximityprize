/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SharpResultantBound
import ArkLib.Data.CodingTheory.ProximityGap.Mu6ConditionalPin

/-!
# The sharp-threshold discharge: the μ = 6 literal-budget pin made UNCONDITIONAL (#371)

`SharpResultantBound.lean` proved the Landau ℓ²-sharpening
`|Res_ℤ(R, Φ_{2^m})|² ≤ 4^{deg R}·(∑|R_i|²)^{2^{m−1}}`.  This file applies it to the
KKH26 collision resultants and discharges the divisibility hypothesis of
`Mu6ConditionalPin.lean`:

1. **`diff_coeff_sq_sum_le`** — a collision difference `sumPoly d₁ − sumPoly d₂` has
   coefficients in `{−2..2}` supported in the window, so `∑|coeff|² ≤ 4·2^{m−1}`.
2. **`natAbs_collisionResultant_sq_le_sharp`** —
   `|N(d₁,d₂)|² ≤ 4^{2^{m−1}−1}·(4·2^{m−1})^{2^{m−1}}` — at `μ = 6`: `≤ 2^{286}`,
   versus the old route's `(2^{192})² = 2^{384}`.
3. **`not_dvd_collisionResultant_of_sq_lt`** — any prime with
   `4^{h−1}·(4h)^h < p²` divides no collision resultant (`collisionResultant_ne_zero`
   supplies nonvanishing) — the threshold drops from `2^{192}` to `≈ 2^{143}`.
4. **`deltaStar_pin_mu6_dim4`** — THE PAYOFF, now unconditional:

   > `mcaDeltaStar(evalCode g 64 3, 1/2¹²⁸) = 59/64` — exactly, no open obligation —

   the dimension-4 (rate 1/16) code on the 64-point smooth domain over
   `P = 1526377·2¹²⁸ + 1` (`P² ≈ 2^{297} > 2^{286}`), beyond Johnson
   (`3/4 < 59/64 < 15/16` = capacity), **at the literal challenge budget on an `n = 64`
   domain** — the first unconditional `δ*` past the old threshold's reach.

Every μ = 6 band of `Mu6LiteralBands.lean` is now equally dischargeable (their primes all
exceed `2^{144}`); this file lands the flagship instance.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 65536
set_option linter.constructorNameAsVariable false

open Polynomial Finset
open scoped NNReal ENNReal
open ArkLib.ProximityGap.KKH26
open ProximityGap ProximityGap.MCAThresholdLedger

namespace ArkLib.ProximityGap.SharpThresholdDischarge

/-! ## The coefficient-square bound for collision differences -/

/-- The difference of two signed sum-polynomials has coefficient squares summing to at
most `4·2^{m−1}` (each coefficient lies in `{−2..2}`, the support lies in the window). -/
theorem diff_coeff_sq_sum_le {m : ℕ} (hm : 1 ≤ m) {U₁ T₁ U₂ T₂ : Finset ℕ}
    (hU₁ : U₁ ⊆ range (2 ^ (m - 1))) (hT₁ : T₁ ⊆ U₁)
    (hU₂ : U₂ ⊆ range (2 ^ (m - 1))) (hT₂ : T₂ ⊆ U₂) :
    (∑ i ∈ (sumPoly U₁ T₁ - sumPoly U₂ T₂).support,
        ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ^ 2)
      ≤ 4 * 2 ^ (m - 1) := by
  classical
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hcoeff : ∀ i, ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ≤ 2 := by
    intro i
    rw [Polynomial.coeff_sub, sumPoly_coeff, sumPoly_coeff]
    split_ifs <;> decide
  have hdeg : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hsupp : (sumPoly U₁ T₁ - sumPoly U₂ T₂).support.card ≤ 2 ^ (m - 1) := by
    calc (sumPoly U₁ T₁ - sumPoly U₂ T₂).support.card
        ≤ (Finset.range ((sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree + 1)).card :=
          Finset.card_le_card (Polynomial.supp_subset_range_natDegree_succ)
    _ = (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree + 1 := Finset.card_range _
    _ ≤ 2 ^ (m - 1) := by omega
  calc (∑ i ∈ (sumPoly U₁ T₁ - sumPoly U₂ T₂).support,
        ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ^ 2)
      ≤ ∑ _i ∈ (sumPoly U₁ T₁ - sumPoly U₂ T₂).support, 4 := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ^ 2
            ≤ 2 ^ 2 := Nat.pow_le_pow_left (hcoeff i) 2
        _ = 4 := by norm_num
  _ = (sumPoly U₁ T₁ - sumPoly U₂ T₂).support.card * 4 := by
        rw [Finset.sum_const, smul_eq_mul]
  _ ≤ 2 ^ (m - 1) * 4 := by
        exact Nat.mul_le_mul_right 4 hsupp
  _ = 4 * 2 ^ (m - 1) := Nat.mul_comm _ _

/-! ## The sharp collision-resultant bound -/

/-- **The sharp collision bound**:
`|N(d₁,d₂)|² ≤ 4^{2^{m−1}−1}·(4·2^{m−1})^{2^{m−1}}` for distinct signed data. -/
theorem natAbs_collisionResultant_sq_le_sharp {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    (collisionResultant m d₁ d₂).natAbs ^ 2
      ≤ 4 ^ (2 ^ (m - 1) - 1) * (4 * 2 ^ (m - 1)) ^ 2 ^ (m - 1) := by
  classical
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, _⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, _⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hdeg : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hbase := ArkLib.ProximityGap.SharpResultantBound.natAbs_resultant_cyclotomic_sq_le
    hm (sumPoly U₁ T₁ - sumPoly U₂ T₂)
  have hsum := diff_coeff_sq_sum_le hm hU₁ hT₁ hU₂ hT₂
  calc (collisionResultant m ⟨U₁, T₁⟩ ⟨U₂, T₂⟩).natAbs ^ 2
      ≤ 4 ^ (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree
        * (∑ i ∈ (sumPoly U₁ T₁ - sumPoly U₂ T₂).support,
            ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ^ 2) ^ 2 ^ (m - 1) := hbase
  _ ≤ 4 ^ (2 ^ (m - 1) - 1) * (4 * 2 ^ (m - 1)) ^ 2 ^ (m - 1) := by
      have h1 : (4 : ℕ) ^ (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree
          ≤ 4 ^ (2 ^ (m - 1) - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (∑ i ∈ (sumPoly U₁ T₁ - sumPoly U₂ T₂).support,
            ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff i).natAbs ^ 2) ^ 2 ^ (m - 1)
          ≤ (4 * 2 ^ (m - 1)) ^ 2 ^ (m - 1) :=
        Nat.pow_le_pow_left hsum _
      exact Nat.mul_le_mul h1 h2

/-! ## The divisibility supply at sharp-threshold primes -/

/-- **The sharp size ⟹ not-dvd supply**: any prime `p` with
`4^{2^{m−1}−1}·(4·2^{m−1})^{2^{m−1}} < p²` divides no collision resultant of distinct
signed data.  At `μ = 6` the left side is `2^{286}`, so every prime above `2^{143}`
qualifies — versus the old `2^{192}` threshold. -/
theorem not_dvd_collisionResultant_of_sq_lt {p : ℕ} [Fact p.Prime] {m r : ℕ}
    (hm : 1 ≤ m)
    (hp : 4 ^ (2 ^ (m - 1) - 1) * (4 * 2 ^ (m - 1)) ^ 2 ^ (m - 1) < p ^ 2) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro d₁ hd₁ d₂ hd₂ hne hdvd
  have hN0 : collisionResultant m d₁ d₂ ≠ 0 :=
    collisionResultant_ne_zero hm hd₁ hd₂ hne
  have hdvdN : p ∣ (collisionResultant m d₁ d₂).natAbs := by
    rw [← Int.natAbs_natCast p]
    exact Int.natAbs_dvd_natAbs.mpr hdvd
  have hple : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hN0) hdvdN
  have hsq : p ^ 2 ≤ (collisionResultant m d₁ d₂).natAbs ^ 2 :=
    Nat.pow_le_pow_left hple 2
  have hbound := natAbs_collisionResultant_sq_le_sharp hm hd₁ hd₂
  omega

/-! ## THE PAYOFF: the μ = 6 literal-budget pin, unconditional -/

local instance localInstance_SharpThresholdDischarge_1 : Fact (Nat.Prime ArkLib.ProximityGap.Mu6ConditionalPin.P) :=
  ⟨ArkLib.ProximityGap.Mu6ConditionalPin.prime_P⟩

/-- **THE UNCONDITIONAL μ = 6 LITERAL-BUDGET PIN**: `δ* = 59/64` exactly at
`ε* = 2⁻¹²⁸` for the dimension-4 (rate 1/16) code on the 64-point smooth domain over
`P = 1526377·2¹²⁸ + 1` — no open obligation.  Beyond Johnson (`3/4 < 59/64`), below
capacity (`15/16`).  The first unconditional in-window pin past the old
`(2^μ)^{2^{μ−1}}` threshold's reach. -/
theorem deltaStar_pin_mu6_dim4 :
    mcaDeltaStar (F := ZMod ArkLib.ProximityGap.Mu6ConditionalPin.P)
        (A := ZMod ArkLib.ProximityGap.Mu6ConditionalPin.P)
        (evalCode
          (343681710474810194684472438365758239853939287 : ZMod ArkLib.ProximityGap.Mu6ConditionalPin.P) 64 3)
        (1 / 2 ^ 128)
      = 59 / 64 := by
  refine ArkLib.ProximityGap.Mu6ConditionalPin.deltaStar_pin_mu6_dim4_of_not_dvd ?_
  have hP2 : 4 ^ (2 ^ (6 - 1) - 1) * (4 * 2 ^ (6 - 1)) ^ 2 ^ (6 - 1)
      < ArkLib.ProximityGap.Mu6ConditionalPin.P ^ 2 := by
    show (4 : ℕ) ^ 31 * 128 ^ 32
        < 519399178373681289045835343167880067297574913 ^ 2
    norm_num
  have h6 : (1 : ℕ) ≤ 6 := by omega
  have h := not_dvd_collisionResultant_of_sq_lt
    (p := ArkLib.ProximityGap.Mu6ConditionalPin.P) (m := 6) (r := 5)
    h6
    hP2
  have he : (2 : ℕ) ^ (6 - 1) = 2 ^ 5 := rfl
  rw [he] at h
  exact h

end ArkLib.ProximityGap.SharpThresholdDischarge

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SharpThresholdDischarge.diff_coeff_sq_sum_le
#print axioms
  ArkLib.ProximityGap.SharpThresholdDischarge.natAbs_collisionResultant_sq_le_sharp
#print axioms
  ArkLib.ProximityGap.SharpThresholdDischarge.not_dvd_collisionResultant_of_sq_lt
#print axioms ArkLib.ProximityGap.SharpThresholdDischarge.deltaStar_pin_mu6_dim4
