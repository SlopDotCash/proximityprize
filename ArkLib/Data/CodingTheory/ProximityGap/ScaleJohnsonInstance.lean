/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GSExactCountWall
import ArkLib.Data.CodingTheory.ProximityGap.GSFullListBound

/-!
# Issue #232 — the Table-1 row-3 list bound AT PRIZE SCALE (n = 2²⁰, ρ = 1/2, within 1.2% of Johnson)

The issue's Table 1, row 3, is the known positive result: list bounds up to the Johnson radius.
`GSFullListBound.gs_full_list_bound` provides the general machine; this file instantiates it at the
**prize's own scale** — domain size `n = 2²⁰`, rate `ρ = 1/2` (`k = 2¹⁹`), the largest prize-relevant
configuration — with multiplicity `m = 64`, agreement `t = 750000`, and weighted-degree budget
`D = 47999999`:

* `gsCount_ge` — the **Gauss minimum** (dual of `GSExactCountWall.two_c_gsCount_le`):
  `D·(D+c) ≤ 2c·gsCount(c,D)`, since `2c·Σ = u(2D+c−u)` with `u = cq ∈ [D, D+c−1]` and
  `u(2D+c−u) − D(D+c) = (u−D)(D+c−u) ≥ 0`.
* `gsSupport_card_eq_gsCount` — the front-end's `#gsSupport(D,k)` IS the exact count `gsCount(k−1,D)`.
* `prize_scale_feasibility` — the GS hypotheses hold at the prize-scale parameters: pure
  (large-numeral, exact) arithmetic `c·n·m·(m+1) < D·(D+c)` chains through the Gauss minimum to
  `n·C(m+1,2) < #gsSupport(D,k)`, and `D < m·t`.
* `prize_scale_johnson_list_bound` (HEADLINE) — for ANY field, ANY `2²⁰` distinct evaluation points,
  ANY received word: every set of polynomials of degree `< 2¹⁹` agreeing on `≥ 750000` of the `2²⁰`
  points has size `≤ 91`.
* `johnson_position` — the Johnson agreement `√(n(k−1))` lies in `(741455, 741456)`, and
  `750000 < 1.012 × 741455`: the certified agreement is within **1.2%** of the Johnson radius at full
  prize scale.  (δ = 1 − 750000/2²⁰ ≈ 0.2848, vs Johnson ≈ 0.2929; and `91 ≪ ε*·|F|` for any
  prize-admissible field.)

This is the known Table-1 row-3 bound, machine-checked end-to-end at the scale the prize fixes.
All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.CodingTheory.PrizeScaleJohnson

open GSExactWall GSHasse Finset

variable {c D : ℕ}

/-- **The Gauss minimum** (dual of `two_c_gsCount_le`): `D·(D+c) ≤ 2c·gsCount(c,D)`.
With `u = c·q ∈ [D, D+c−1]`, the doubled sum is exactly `u(2D+c−u)`, and
`u(2D+c−u) − D(D+c) = (u−D)(D+c−u) ≥ 0`. -/
theorem gsCount_ge (hc : 0 < c) (hD : 0 < D) :
    D * (D + c) ≤ 2 * c * gsCount c D := by
  rw [gsCount_eq_sum_q hc hD]
  set q := qIdx c D with hq
  have hterm : ∀ j ∈ Finset.range q, c * j < D := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj' : j + 1 ≤ q := by omega
    have h1 : c * (j + 1) ≤ c * q := Nat.mul_le_mul_left c hj'
    have h2 := qIdx_le (D := D) hc
    rw [← hq] at h2
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  -- the doubled sum over ℤ (Gauss)
  have hgauss : (2 * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
      = 2 * q * D - c * (q * (q - 1)) := by
    have hcast : ((∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
        = ∑ j ∈ Finset.range q, ((D : ℤ) - c * j) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h := hterm j hj
      rw [Nat.cast_sub (le_of_lt h)]
      push_cast
      ring
    rw [hcast, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
        nsmul_eq_mul]
    have hgsum : (∑ j ∈ Finset.range q, (j : ℤ)) * 2 = q * ((q : ℤ) - 1) := by
      have h := Finset.sum_range_id_mul_two q
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · rw [hq0]; simp
      · calc (∑ j ∈ Finset.range q, (j : ℤ)) * 2
            = (((∑ j ∈ Finset.range q, j) * 2 : ℕ) : ℤ) := by push_cast [Nat.cast_sum]; ring
          _ = ((q * (q - 1) : ℕ) : ℤ) := by rw [h]
          _ = q * ((q : ℤ) - 1) := by
              push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
              ring
    linear_combination (-(c : ℤ)) * hgsum
  have hu_ge : (D : ℤ) ≤ c * q := by
    have h := qIdx_ge hc hD
    rw [← hq] at h
    exact_mod_cast h
  have hu_le : (c * q : ℤ) ≤ (D : ℤ) + c - 1 := by
    have h := qIdx_le (D := D) hc
    rw [← hq] at h
    have h' : ((c * q : ℕ) : ℤ) ≤ ((D + c - 1 : ℕ) : ℤ) := Nat.cast_le.mpr h
    have hDc : 1 ≤ D + c := by omega
    rw [Nat.cast_sub hDc] at h'
    push_cast at h' ⊢
    omega
  have hexp : (2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
      = (c * q) * (2 * D + c - c * q) := by
    have h2 : (2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
        = c * (2 * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ) := by ring
    rw [h2, hgauss]
    ring
  have hmain : ((D : ℤ) * (D + c)) ≤ 2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) := by
    rw [hexp]
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (c*q : ℤ) - D)
      (by linarith : (0:ℤ) ≤ (D : ℤ) + c - c * q)]
  exact_mod_cast hmain

/-- The interpolation front-end's monomial count IS the exact lattice count:
`#gsSupport(D,k) = gsCount(k−1, D)` (both are `∑_{j<D}(D−(k−1)j)`). -/
theorem gsSupport_card_eq_gsCount (D k : ℕ) :
    (GSHasse.gsSupport D k).card = gsCount (k - 1) D := by
  rw [GSHasse.gsSupport_card, gsCount]

/-! ## The prize-scale parameters: `n = 2²⁰`, `k = 2¹⁹` (`ρ = 1/2`), `m = 64`, `t = 750000`,
`D = 47999999`. -/

/-- **Prize-scale feasibility.**  Both `gs_full_list_bound` hypotheses hold at
`n = 2²⁰, k = 2¹⁹, m = 64, t = 750000, D = 47999999`:
the constraint excess via `c·n·m·(m+1) < D·(D+c)` (exact large-numeral arithmetic) chained through
the Gauss minimum, and the root-order budget `D < m·t`. -/
theorem prize_scale_feasibility :
    2 ^ 20 * (64 + 1).choose 2 < (GSHasse.gsSupport 47999999 (2 ^ 19)).card ∧
    47999999 < 64 * 750000 := by
  constructor
  · rw [gsSupport_card_eq_gsCount]
    set c : ℕ := 2 ^ 19 - 1 with hc
    have hcpos : 0 < c := by norm_num [hc]
    have hDpos : 0 < 47999999 := by norm_num
    have hge := gsCount_ge (c := c) (D := 47999999) hcpos hDpos
    -- 2c·(n·C(65,2)) = c·n·64·65 < D·(D+c) ≤ 2c·gsCount ⟹ n·C(65,2) < gsCount
    have harith : 2 * c * (2 ^ 20 * (64 + 1).choose 2) < 47999999 * (47999999 + c) := by
      rw [hc]
      norm_num [Nat.choose_two_right]
    have hchain : 2 * c * (2 ^ 20 * (64 + 1).choose 2)
        < 2 * c * gsCount c 47999999 := lt_of_lt_of_le harith hge
    exact Nat.lt_of_mul_lt_mul_left hchain
  · norm_num

/-- **HEADLINE — the Table-1 row-3 list bound at prize scale.**  For ANY field `F`, ANY `2²⁰`
distinct evaluation points, ANY received word `w`: every finite set of polynomials of degree
`< 2¹⁹` (rate `ρ = 1/2`), each agreeing with `w` on at least `750000` of the `2²⁰` points
(relative radius `δ ≈ 0.2848`, within 1.2% of the Johnson radius `≈ 0.2929`), has size at most

  `(47999999 − 1)/(2¹⁹ − 1) = 91`.

`91` is far below `ε*·|F|` for any prize-admissible field — the known-positive regime of Table 1,
machine-checked end-to-end at the prize's own scale. -/
theorem prize_scale_johnson_list_bound {F : Type*} [Field F] [DecidableEq F]
    (α w : Fin (2 ^ 20) → F) (hinj : Function.Injective α)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 2 ^ 19 - 1)
    (hagree : ∀ f ∈ L,
      750000 ≤ (Finset.univ.filter fun s : Fin (2 ^ 20) => f.eval (α s) = w s).card) :
    L.card ≤ 91 := by
  have h := ArkLib.CodingTheory.GSFullListBound.gs_full_list_bound
    (2 ^ 19) 47999999 64 750000 (2 ^ 20) (by norm_num) (by norm_num)
    α w hinj prize_scale_feasibility.1
    (by norm_num) L hdeg hagree
  calc L.card ≤ (47999999 - 1) / (2 ^ 19 - 1) := h
    _ = 91 := by decide

/-- **Position relative to Johnson.**  The Johnson agreement `√(n(k−1))` at `n = 2²⁰, k = 2¹⁹`
lies strictly between `741454` and `741455`, and the certified agreement `750000` satisfies
`750000 × 1000 < 741456 × 1012` — i.e. it is within `1.2%` of the Johnson radius, at full prize
scale. -/
theorem johnson_position :
    741454 ^ 2 < 2 ^ 20 * (2 ^ 19 - 1) ∧
    2 ^ 20 * (2 ^ 19 - 1) < 741455 ^ 2 ∧
    750000 * 1000 < 741455 * 1012 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end ArkLib.CodingTheory.PrizeScaleJohnson

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.PrizeScaleJohnson.gsCount_ge
#print axioms ArkLib.CodingTheory.PrizeScaleJohnson.prize_scale_feasibility
#print axioms ArkLib.CodingTheory.PrizeScaleJohnson.prize_scale_johnson_list_bound
#print axioms ArkLib.CodingTheory.PrizeScaleJohnson.johnson_position
