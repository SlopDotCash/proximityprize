/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import ArkLib.ToMathlib.NumberTheory.GaussSumNorm

/-!
# Constant-index √-cancellation: the worst-case per-frequency bound for ANY fixed-index subgroup (#407)

This file generalizes `QRWorstCaseIncompleteSum.lean` (index 2) to **every constant index `m`**: the
worst-case incomplete sum over the index-`m` multiplicative subgroup `G = {a : χ(a)=1}` (`χ` a
character of order `m`) is bounded by the classical Gauss sums, giving square-root cancellation
`‖η_b‖ ≤ ((m−1)√q + 1)/m ≈ √m·√n` — PROVEN, no wall.

## Brick 1 (this commit): the general Gauss-sum magnitude `‖gaussSum χ ψ‖ = √q`

Mathlib has `gaussSum_mul_gaussSum_eq_card` (`g(χ)·g(χ⁻¹,ψ⁻¹) = q` for `χ ≠ 1`) but NOT the magnitude
directly.  Over `ℂ`, `g(χ⁻¹,ψ⁻¹) = conj(g(χ,ψ))` (characters are unit-circle valued), so
`‖g(χ,ψ)‖² = g(χ,ψ)·conj(g(χ,ψ)) = q`, hence `‖g(χ,ψ)‖ = √q`.  This is the index-`m` companion of the
in-tree `gaussSum_normSq` (which is the quadratic special case via `gaussSum_sq`).
-/

set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.ConstantIndexGaussSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `‖χ(a)‖ = 1` for every nonzero `a` (character values are roots of unity). -/
theorem norm_mulChar_unit (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card F - 1) ?_ (by omega)
  rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]

/-- Conjugation sends the Gauss sum of `(χ, ψ)` to that of `(χ⁻¹, ψ⁻¹)`. -/
theorem conj_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, AddChar.starComp_apply hchar, starRingEnd_apply, MulChar.star_apply']

/-- **The general Gauss-sum magnitude** `‖gaussSum χ ψ‖ = √q` for any nontrivial `χ` and primitive
`ψ` over a finite field, valued in `ℂ`.  Reusable; Mathlib lacks it directly. -/
theorem norm_gaussSum_eq_sqrt {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) :=
  _root_.norm_gaussSum_eq_sqrt_card hχ hψ

/-- **Character orthogonality / indicator decomposition.** For a multiplicative character `χ` of
order `m = orderOf χ`, the subgroup-indicator of `G_χ = {a : χ a = 1}` is the average of the powers
of `χ`:  `∑_{j<m} (χ^j) a = m·[χ a = 1]`.  (Geometric series in `χ a`, using `χ^m = 1`.) -/
theorem mulChar_pow_sum_all (χ : MulChar F ℂ) (a : F) :
    ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a = if χ a = 1 then (orderOf χ : ℂ) else 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : ∀ j ∈ Finset.range (orderOf χ), (χ ^ j) (0 : F) = 0 :=
      fun j _ => MulChar.map_nonunit (χ ^ j) not_isUnit_zero
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, if_neg]
    rw [MulChar.map_nonunit χ not_isUnit_zero]; exact zero_ne_one
  · have hunit : IsUnit a := ha.isUnit
    have hval : ∀ j, (χ ^ j) a = (χ a) ^ j := by
      intro j
      have h := MulChar.pow_apply_coe χ j hunit.unit
      rwa [IsUnit.unit_spec] at h
    rw [Finset.sum_congr rfl (fun j _ => hval j)]
    by_cases h : χ a = 1
    · rw [if_pos h, h]; simp
    · rw [if_neg h, geom_sum_eq h]
      have hm : (χ a) ^ (orderOf χ) = 1 := by
        have hp := MulChar.pow_apply_coe χ (orderOf χ) hunit.unit
        rw [IsUnit.unit_spec] at hp
        rw [← hp, pow_orderOf_eq_one χ, MulChar.one_apply hunit]
      rw [hm, sub_self, zero_div]

/-- The index-`m` multiplicative subgroup `G_χ = {a : χ a = 1}` cut out by `χ` (`m = orderOf χ`). -/
noncomputable def Gchi (χ : MulChar F ℂ) : Finset F :=
  Finset.univ.filter (fun a => χ a = 1)

/-- **The index-`m` period decomposition.** `m·η_b(G_χ) = ∑_{j<m} gaussSum(χ^j, ψ_b)`, `ψ_b = ψ(b·)`.
The subgroup period over `G_χ` is the average of the `m` twisted Gauss sums — the index-`m`
generalization of the index-2 `eta_QR_eq`. -/
theorem eta_constIndex_decomp (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (b : F) :
    (orderOf χ : ℂ) * eta ψ (Gchi χ) b
      = ∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b) := by
  classical
  symm
  calc ∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b)
      = ∑ j ∈ Finset.range (orderOf χ), ∑ a : F, (χ ^ j) a * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [gaussSum]
        exact Finset.sum_congr rfl (fun a _ => by rw [AddChar.mulShift_apply])
    _ = ∑ a : F, ∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a * ψ (b * a) := Finset.sum_comm
    _ = ∑ a : F, (∑ j ∈ Finset.range (orderOf χ), (χ ^ j) a) * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_mul]
    _ = ∑ a : F, (if χ a = 1 then (orderOf χ : ℂ) else 0) * ψ (b * a) := by
        refine Finset.sum_congr rfl (fun a _ => by rw [mulChar_pow_sum_all])
    _ = ∑ a : F, if χ a = 1 then (orderOf χ : ℂ) * ψ (b * a) else 0 := by
        refine Finset.sum_congr rfl (fun a _ => ?_); simp only [ite_mul, zero_mul]
    _ = ∑ a ∈ Gchi χ, (orderOf χ : ℂ) * ψ (b * a) := by rw [Gchi, Finset.sum_filter]
    _ = (orderOf χ : ℂ) * ∑ a ∈ Gchi χ, ψ (b * a) := by rw [Finset.mul_sum]
    _ = (orderOf χ : ℂ) * eta ψ (Gchi χ) b := by rw [eta]

/-- The principal (`j=0`) term: `gaussSum(1, ψ') = −1` for any nontrivial `ψ'`. -/
theorem gaussSum_one_eq_neg_one {ψ' : AddChar F ℂ} (hψ' : ψ' ≠ 1) :
    gaussSum (1 : MulChar F ℂ) ψ' = -1 := by
  rw [gaussSum]
  have h1 : ∀ a : F, (1 : MulChar F ℂ) a * ψ' a = ψ' a - (if a = 0 then ψ' a else 0) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · rw [MulChar.map_nonunit (1 : MulChar F ℂ) not_isUnit_zero, zero_mul, if_pos rfl]; ring
    · rw [MulChar.one_apply ha.isUnit, one_mul, if_neg ha]; ring
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ 0 (fun a => ψ' a), if_pos (Finset.mem_univ 0),
    AddChar.sum_eq_zero_of_ne_one hψ', AddChar.map_zero_eq_one, zero_sub]

/-- `mulShift ψ b` is primitive when `ψ` is primitive and `b ≠ 0`. -/
theorem mulShift_isPrimitive {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    (AddChar.mulShift ψ b).IsPrimitive := by
  intro c hc
  rw [AddChar.mulShift_mulShift]
  exact hψ (mul_ne_zero hb hc)

/-- Each twisted Gauss sum `gaussSum(χ^j, ψ_b)` with `0 < j < m` has magnitude `√q`. -/
theorem norm_gaussSum_pow_eq {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) {j : ℕ} (hj0 : j ≠ 0) (hjm : j < orderOf χ) :
    ‖gaussSum (χ ^ j) (AddChar.mulShift ψ b)‖ = Real.sqrt (Fintype.card F : ℝ) :=
  norm_gaussSum_eq_sqrt (pow_ne_one_of_lt_orderOf hj0 hjm) (mulShift_isPrimitive hψ hb)

/-- **The constant-index √-cancellation bound.**  For the index-`m` subgroup `G_χ` (`m = orderOf χ ≥ 2`)
and any frequency `b ≠ 0`, the period satisfies
  `‖η_b(G_χ)‖ ≤ ((m−1)·√q + 1)/m`.
Since `|G_χ| = (q−1)/m`, this is `‖η_b‖ ≲ √m·√n` — genuine square-root cancellation for every
CONSTANT index `m`, PROVEN via the classical Gauss sums (no wall).  Generalizes the index-2
`eta_QR_norm_le`. -/
theorem eta_constIndex_norm_le {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (hm : 2 ≤ orderOf χ) :
    ‖eta ψ (Gchi χ) b‖
      ≤ ((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ) := by
  have hmpos : (0 : ℝ) < (orderOf χ : ℝ) := by exact_mod_cast (by omega : 0 < orderOf χ)
  have h0mem : (0 : ℕ) ∈ Finset.range (orderOf χ) := Finset.mem_range.mpr (by omega)
  have hψb1 : AddChar.mulShift ψ b ≠ 1 := hψ hb
  -- bound the sum of the m twisted Gauss sums
  have hsum_le : ‖∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b)‖
      ≤ 1 + (orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    rw [← Finset.add_sum_erase _ _ h0mem]
    refine le_trans (norm_add_le _ _) ?_
    have hterm0 : ‖gaussSum (χ ^ 0) (AddChar.mulShift ψ b)‖ = 1 := by
      rw [pow_zero, gaussSum_one_eq_neg_one hψb1, norm_neg, norm_one]
    have hbound : ∀ j ∈ (Finset.range (orderOf χ)).erase 0,
        ‖gaussSum (χ ^ j) (AddChar.mulShift ψ b)‖ = Real.sqrt (Fintype.card F : ℝ) := by
      intro j hj
      rw [Finset.mem_erase, Finset.mem_range] at hj
      exact norm_gaussSum_pow_eq hψ hb hj.1 hj.2
    have hcard : ((Finset.range (orderOf χ)).erase 0).card = orderOf χ - 1 := by
      rw [Finset.card_erase_of_mem h0mem, Finset.card_range]
    have heq : ∑ j ∈ (Finset.range (orderOf χ)).erase 0,
        ‖gaussSum (χ ^ j) (AddChar.mulShift ψ b)‖
        = (orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
      rw [Finset.sum_congr rfl hbound, Finset.sum_const, nsmul_eq_mul, hcard,
        Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
    have htail := le_trans (norm_sum_le ((Finset.range (orderOf χ)).erase 0)
      (fun j => gaussSum (χ ^ j) (AddChar.mulShift ψ b))) (le_of_eq heq)
    rw [hterm0]
    linarith [htail]
  -- m * ‖eta‖ = ‖m * eta‖ = ‖sum‖ ≤ 1 + (m-1)√q
  have hkey : (orderOf χ : ℝ) * ‖eta ψ (Gchi χ) b‖
      ≤ 1 + (orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    have hnorm : (orderOf χ : ℝ) * ‖eta ψ (Gchi χ) b‖
        = ‖∑ j ∈ Finset.range (orderOf χ), gaussSum (χ ^ j) (AddChar.mulShift ψ b)‖ := by
      rw [← eta_constIndex_decomp χ ψ b, norm_mul, Complex.norm_natCast]
    rw [hnorm]; exact hsum_le
  rw [le_div_iff₀ hmpos]
  nlinarith [hkey]

/-- **The named open per-frequency core, discharged for every constant-index subgroup.**
`WorstCaseIncompleteSumBound ψ (G_χ) (((m−1)√q + 1)/m)²` holds unconditionally (`m = orderOf χ ≥ 2`),
via the classical Gauss sums. -/
theorem worstCaseIncompleteSumBound_constIndex {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (hm : 2 ≤ orderOf χ) :
    ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum.WorstCaseIncompleteSumBound ψ (Gchi χ)
      ((((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) ^ 2) := by
  intro b hb
  have hle := eta_constIndex_norm_le hψ hb hm
  have hnn : (0 : ℝ) ≤ ‖eta ψ (Gchi χ) b‖ := norm_nonneg _
  gcongr

/-- **End-to-end additive-energy budget** for the index-`m` subgroup.  Feeding the worst-case bound
into the in-tree consumer `addEnergy_le_of_worstCase` gives an unconditional envelope
`q·E(G_χ) ≤ |G_χ|⁴ + (((m−1)√q+1)/m)²·(q·|G_χ|)` — no regime hypothesis. -/
theorem addEnergy_constIndex_le {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hm : 2 ≤ orderOf χ) :
    (Fintype.card F : ℝ)
        * (ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy (Gchi χ) : ℝ)
      ≤ (Gchi χ).card ^ 4
        + ((((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) ^ 2)
          * ((Fintype.card F : ℝ) * (Gchi χ).card) := by
  refine ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum.addEnergy_le_of_worstCase hψ (Gchi χ)
    ?_ (worstCaseIncompleteSumBound_constIndex hψ hm)
  positivity

end ArkLib.ProximityGap.ConstantIndexGaussSum

#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.addEnergy_constIndex_le
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_mulChar_unit
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.conj_gaussSum
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_gaussSum_eq_sqrt
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.mulChar_pow_sum_all
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.eta_constIndex_decomp
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.eta_constIndex_norm_le
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.worstCaseIncompleteSumBound_constIndex
