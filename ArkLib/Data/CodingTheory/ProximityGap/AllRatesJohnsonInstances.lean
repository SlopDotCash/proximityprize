/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ScaleJohnsonInstance

/-!
# Issue #232 — Table-1 row 3 at prize scale, for ALL FOUR prize rates

`PrizeScaleJohnsonInstance` delivered the rate-`1/2` row (`n = 2²⁰, k = 2¹⁹`: list `≤ 91` at
agreement `750000`, within 1.2% of Johnson).  This file completes the table at the remaining prize
rates `ρ ∈ {1/4, 1/8, 1/16}` (same domain size `n = 2²⁰`, multiplicity `m = 64`), reusing the
`gsCount_ge` Gauss-minimum engine:

| ρ | k | Johnson agreement `√(n(k−1))` | certified `t` | within | list cap |
|---|---|---|---|---|---|
| 1/4  | 2¹⁸ | ∈ (524286, 524287) | **529000** | 0.9% | 129 |
| 1/8  | 2¹⁷ | ∈ (370726, 370727) | **374000** | 0.9% | 182 |
| 1/16 | 2¹⁶ | ∈ (262141, 262142) | **264200** | 0.8% | 258 |

Each rung: the feasibility `c·n·m·(m+1) < D·(D+c)` is exact large-numeral arithmetic, chained
through the Gauss minimum to the interpolant count, with `D = 64·t − 1`; the cap is
`(D−1)/(k−1)`.  All caps are `≪ ε*·|F|` for any prize-admissible field.  With the rate-`1/2` row
this is the complete known-positive regime of the issue's Table 1, machine-checked end-to-end at
the prize's own four rates.  All results are `sorry`-free and axiom-clean. -/

namespace ArkLib.CodingTheory.PrizeAllRatesJohnson

open ArkLib.CodingTheory.PrizeScaleJohnson GSExactWall GSHasse

/-! ## Rate 1/4: `k = 2¹⁸`, `t = 529000`, `D = 33855999`, cap `129`. -/

/-- Feasibility at rate `1/4`. -/
theorem feasibility_quarter :
    2 ^ 20 * (64 + 1).choose 2 < (GSHasse.gsSupport 33855999 (2 ^ 18)).card ∧
    33855999 < 64 * 529000 := by
  constructor
  · rw [gsSupport_card_eq_gsCount]
    set c : ℕ := 2 ^ 18 - 1 with hc
    have hcpos : 0 < c := by norm_num [hc]
    have hge := gsCount_ge (c := c) (D := 33855999) hcpos (by norm_num)
    have harith : 2 * c * (2 ^ 20 * (64 + 1).choose 2) < 33855999 * (33855999 + c) := by
      rw [hc]
      norm_num [Nat.choose_two_right]
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le harith hge)
  · norm_num

/-- **Rate `1/4` list bound at prize scale:** every set of degree-`< 2¹⁸` polynomials with
`≥ 529000` agreements (of `2²⁰` points) has size `≤ 129`. -/
theorem list_bound_quarter {F : Type*} [Field F] [DecidableEq F]
    (α w : Fin (2 ^ 20) → F) (hinj : Function.Injective α)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 2 ^ 18 - 1)
    (hagree : ∀ f ∈ L,
      529000 ≤ (Finset.univ.filter fun s : Fin (2 ^ 20) => f.eval (α s) = w s).card) :
    L.card ≤ 129 := by
  have h := ArkLib.CodingTheory.GSFullListBound.gs_full_list_bound
    (2 ^ 18) 33855999 64 529000 (2 ^ 20) (by norm_num) (by norm_num)
    α w hinj feasibility_quarter.1 (by norm_num) L hdeg hagree
  calc L.card ≤ (33855999 - 1) / (2 ^ 18 - 1) := h
    _ = 129 := by decide

/-- Johnson position at rate `1/4`: `√(n(k−1)) ∈ (524286, 524287)`, and
`529000` is within `0.9%`. -/
theorem johnson_position_quarter :
    524286 ^ 2 < 2 ^ 20 * (2 ^ 18 - 1) ∧ 2 ^ 20 * (2 ^ 18 - 1) < 524287 ^ 2 ∧
    529000 * 1000 < 524287 * 1009 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Rate 1/8: `k = 2¹⁷`, `t = 374000`, `D = 23935999`, cap `182`. -/

/-- Feasibility at rate `1/8`. -/
theorem feasibility_eighth :
    2 ^ 20 * (64 + 1).choose 2 < (GSHasse.gsSupport 23935999 (2 ^ 17)).card ∧
    23935999 < 64 * 374000 := by
  constructor
  · rw [gsSupport_card_eq_gsCount]
    set c : ℕ := 2 ^ 17 - 1 with hc
    have hcpos : 0 < c := by norm_num [hc]
    have hge := gsCount_ge (c := c) (D := 23935999) hcpos (by norm_num)
    have harith : 2 * c * (2 ^ 20 * (64 + 1).choose 2) < 23935999 * (23935999 + c) := by
      rw [hc]
      norm_num [Nat.choose_two_right]
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le harith hge)
  · norm_num

/-- **Rate `1/8` list bound at prize scale:** every set of degree-`< 2¹⁷` polynomials with
`≥ 374000` agreements has size `≤ 182`. -/
theorem list_bound_eighth {F : Type*} [Field F] [DecidableEq F]
    (α w : Fin (2 ^ 20) → F) (hinj : Function.Injective α)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 2 ^ 17 - 1)
    (hagree : ∀ f ∈ L,
      374000 ≤ (Finset.univ.filter fun s : Fin (2 ^ 20) => f.eval (α s) = w s).card) :
    L.card ≤ 182 := by
  have h := ArkLib.CodingTheory.GSFullListBound.gs_full_list_bound
    (2 ^ 17) 23935999 64 374000 (2 ^ 20) (by norm_num) (by norm_num)
    α w hinj feasibility_eighth.1 (by norm_num) L hdeg hagree
  calc L.card ≤ (23935999 - 1) / (2 ^ 17 - 1) := h
    _ = 182 := by decide

/-- Johnson position at rate `1/8`: `√(n(k−1)) ∈ (370726, 370727)`, and
`374000` is within `0.9%`. -/
theorem johnson_position_eighth :
    370726 ^ 2 < 2 ^ 20 * (2 ^ 17 - 1) ∧ 2 ^ 20 * (2 ^ 17 - 1) < 370727 ^ 2 ∧
    374000 * 1000 < 370727 * 1009 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Rate 1/16: `k = 2¹⁶`, `t = 264200`, `D = 16908799`, cap `258`. -/

/-- Feasibility at rate `1/16`. -/
theorem feasibility_sixteenth :
    2 ^ 20 * (64 + 1).choose 2 < (GSHasse.gsSupport 16908799 (2 ^ 16)).card ∧
    16908799 < 64 * 264200 := by
  constructor
  · rw [gsSupport_card_eq_gsCount]
    set c : ℕ := 2 ^ 16 - 1 with hc
    have hcpos : 0 < c := by norm_num [hc]
    have hge := gsCount_ge (c := c) (D := 16908799) hcpos (by norm_num)
    have harith : 2 * c * (2 ^ 20 * (64 + 1).choose 2) < 16908799 * (16908799 + c) := by
      rw [hc]
      norm_num [Nat.choose_two_right]
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le harith hge)
  · norm_num

/-- **Rate `1/16` list bound at prize scale:** every set of degree-`< 2¹⁶` polynomials with
`≥ 264200` agreements has size `≤ 258`. -/
theorem list_bound_sixteenth {F : Type*} [Field F] [DecidableEq F]
    (α w : Fin (2 ^ 20) → F) (hinj : Function.Injective α)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 2 ^ 16 - 1)
    (hagree : ∀ f ∈ L,
      264200 ≤ (Finset.univ.filter fun s : Fin (2 ^ 20) => f.eval (α s) = w s).card) :
    L.card ≤ 258 := by
  have h := ArkLib.CodingTheory.GSFullListBound.gs_full_list_bound
    (2 ^ 16) 16908799 64 264200 (2 ^ 20) (by norm_num) (by norm_num)
    α w hinj feasibility_sixteenth.1 (by norm_num) L hdeg hagree
  calc L.card ≤ (16908799 - 1) / (2 ^ 16 - 1) := h
    _ = 258 := by decide

/-- Johnson position at rate `1/16`: `√(n(k−1)) ∈ (262141, 262142)`, and `264200` is within
`0.8%`. -/
theorem johnson_position_sixteenth :
    262141 ^ 2 < 2 ^ 20 * (2 ^ 16 - 1) ∧ 2 ^ 20 * (2 ^ 16 - 1) < 262142 ^ 2 ∧
    264200 * 1000 < 262142 * 1008 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end ArkLib.CodingTheory.PrizeAllRatesJohnson

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.list_bound_quarter
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.list_bound_eighth
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.list_bound_sixteenth
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.johnson_position_quarter
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.johnson_position_eighth
#print axioms ArkLib.CodingTheory.PrizeAllRatesJohnson.johnson_position_sixteenth
