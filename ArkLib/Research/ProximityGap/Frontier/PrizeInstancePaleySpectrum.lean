/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan
import ArkLib.Research.ProximityGap.Frontier.ConcreteTrivialCeiling
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldPeriodAlignment
import ArkLib.Research.ProximityGap.Frontier.ShawFlatnessSubfieldCounterexample
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The periodic sums on the order-128 domain solving both coding prizes

On the inclusion of the 128th roots of unity in the field of order
`65 * 2^239 + 1`, the logarithmic bound with constant one follows from the
triangle inequality. Simultaneous alignment on the 64 antipodal pairs also
produces a nonzero frequency of magnitude greater than 64. These bounds
concern precisely the connection set used as the Reed–Solomon domain.
-/

namespace ProximityGap.PrizeInstancePaleySpectrum

open ArkLib.ProximityGap
open SubgroupGaussSumSecondMoment (eta)
open Round8CosetConcentration (sgFinset sgFinset_card)
open Code GrandChallenges FourRateListPrime246

/-- When the logarithm dominates the cardinality, every character satisfies
the base-two logarithmic bound with constant one. -/
theorem shawGapLaw_one_of_card_le_log {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (D : Finset F)
    (h : (D.card : ℝ) ≤ Real.logb 2 ((Fintype.card F : ℝ) / D.card)) :
    ProximityPrize.ShawGapLaw ψ D 1 := by
  intro b _
  rw [one_mul]
  apply (Frontier.ConcreteTrivialCeiling.norm_eta_le_card ψ D b).trans
  rw [← Real.sqrt_sq (Nat.cast_nonneg D.card)] at ⊢
  apply Real.sqrt_le_sqrt
  simpa [sq] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg D.card)

private theorem card_domain : (sgFinset H).card = 128 := (sgFinset_card H).trans card_H

/-- The logarithmic bound on this domain holds for every additive character. -/
theorem prime246_shawGapLaw (ψ : AddChar K ℂ) : ProximityPrize.ShawGapLaw ψ (sgFinset H) 1 := by
  apply shawGapLaw_one_of_card_le_log
  rw [card_K, card_domain]
  have h : (2 : ℝ)^128 ≤ (P : ℝ) / 128 := by norm_num [P]
  exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    (by simpa using h)

/-- A nonprincipal period of the same domain exceeds half its degree. -/
theorem prime246_large_period :
    ∃ b : K, b ≠ 0 ∧ 64 < ‖eta ZMod.stdAddChar (sgFinset H) b‖ := by
  classical
  have hneg : ∀ x ∈ sgFinset H, -x ∈ sgFinset H := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have hu : -(u : Kˣ) ∈ H := by
      apply (mem_rootsOfUnity' 128 _).mpr
      simpa only [Units.val_neg, Even.neg_pow (by decide : Even 128)] using
        (mem_rootsOfUnity' 128 (u : Kˣ)).mp u.property
    exact Finset.mem_image.mpr ⟨⟨-(u : Kˣ), hu⟩, Finset.mem_univ _, rfl⟩
  have hz : (0 : K) ∉ sgFinset H := by
    intro hx
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
    exact (u : Kˣ).ne_zero hu
  obtain ⟨b, hb, h⟩ := PrimeFieldPeriodAlignment.large_period_of_antipodal (sgFinset H)
    (Finset.card_pos.mp (card_domain ▸ by decide)) (by decide) hz hneg
    (card_domain ▸ by decide)
  exact ⟨b, hb, by norm_num [card_domain] at h; exact h⟩

/-- Both coding prizes coexist with the logarithmic bound and with failure of
the historical `2√n` spectral ceiling on their actual domain. -/
theorem prime246_both_prizes_and_spectrum (m : ℕ) (hm : 0 < m) :
    (mcaPrize domain ∧ listDecodingPrize domain m) ∧
    ProximityPrize.ShawGapLaw ZMod.stdAddChar (sgFinset H) 1 ∧
    ¬ GeneralizedPaleyRamanujan.GeneralizedPaleyRamanujan ZMod.stdAddChar (sgFinset H) := by
  refine ⟨FourRateSmoothMca128.prime246_both_prizes m hm, prime246_shawGapLaw _, ?_⟩
  intro h
  obtain ⟨b, hb, hlarge⟩ := prime246_large_period
  have hupper := h b hb
  rw [card_domain] at hupper
  have hs : Real.sqrt (128 : ℝ) ≤ 32 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  norm_num only [Nat.cast_ofNat] at hupper
  linarith

/-! ## Quadratic-character discrepancy of the same set in the classical Paley graph -/

open BinaryPower (binaryPow binaryPow_eq_pow)

private def eulerSign (x : K) : ℤ :=
  if x = 0 then 0 else if binaryPow x (P / 2) = 1 then 1 else -1

private theorem eulerSign_eq (x : K) : eulerSign x = quadraticChar K x := by
  by_cases hx : x = 0
  · simp [eulerSign, hx]
  · have hchar : ringChar K ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
    simp only [eulerSign, hx, ↓reduceIte, binaryPow_eq_pow,
      quadraticChar_eq_pow_of_char_ne_two hchar hx, card_K]

private def atPower (i : Fin 128) : H := generator_primitive.toRootsOfUnity ^ (i : ℕ)

private theorem eval_atPower (i : Fin 128) : domain (atPower i) = generator ^ (i : ℕ) := rfl

private theorem atPower_bijective : Function.Bijective atPower := by
  constructor
  · intro i j hij
    apply Fin.ext
    exact generator_primitive.pow_inj i.isLt j.isLt (congrArg domain hij)
  · intro u
    obtain ⟨i, hi, heq⟩ := generator_primitive.eq_pow_of_pow_eq_one
      ((mem_rootsOfUnity' 128 (u : Kˣ)).mp u.property)
    exact ⟨⟨i, hi⟩, domain.injective heq⟩

private theorem chi_of_mem (x : H) : quadraticChar K (domain x) = 1 := by
  have hchar : ringChar K ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have hx : domain x ≠ 0 := (x : Kˣ).ne_zero
  rw [quadraticChar_eq_pow_of_char_ne_two hchar hx, card_K]
  have hpow := (mem_rootsOfUnity' 128 (x : Kˣ)).mp x.property
  rw [show P / 2 = 128 * (P / 256) by decide, pow_mul]
  simp [show domain x ^ 128 = 1 from hpow]

set_option maxRecDepth 10000 in
private theorem euler_row :
    (List.ofFn (fun i : Fin 128 => eulerSign (1 - binaryPow generator (i : ℕ)))).sum = 7 := by
  decide

private theorem row_at_one : ∑ y : H, quadraticChar K (1 - domain y) = 7 := by
  rw [← atPower_bijective.sum_comp (fun y => quadraticChar K (1 - domain y))]
  simpa only [List.sum_ofFn, binaryPow_eq_pow, eulerSign_eq, eval_atPower] using euler_row

/-- At each point of the coding domain the classical Paley character sums to seven
across the domain, counting the zero on the diagonal. -/
theorem prime246_quadratic_row (x : H) : ∑ y : H, quadraticChar K (domain x - domain y) = 7 := by
  rw [← (Group.mulLeft_bijective x).sum_comp (fun y : H => quadraticChar K (domain x - domain y))]
  calc
    _ = ∑ y : H, quadraticChar K (1 - domain y) := by
      apply Finset.sum_congr rfl
      intro y _
      have hxy : domain (x*y) = domain x * domain y := rfl
      rw [hxy, ← mul_one_sub, map_mul, chi_of_mem, one_mul]
    _ = 7 := row_at_one

/-- Every vertex has 67 neighbors in the subgraph of the classical Paley graph
induced on the evaluation subgroup. -/
theorem prime246_induced_degree (x : H) :
    (Finset.univ.filter (fun y : H => quadraticChar K (domain x - domain y) = 1)).card = 67 := by
  classical
  let f (y : H) := quadraticChar K (domain x - domain y)
  have hpoint (y : H) : 2 * (if f y = 1 then (1 : ℤ) else 0) =
      f y + 1 - (if y = x then 1 else 0) := by
    by_cases hy : y = x
    · subst y
      simp [f]
    · have hne : domain x - domain y ≠ 0 := sub_ne_zero.mpr (domain.injective.ne (Ne.symm hy))
      rcases (show f y = 1 ∨ f y = -1 from quadraticChar_dichotomy hne) with h | h <;>
        rw [h] <;> norm_num [hy]
  have heq := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => hpoint y)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at heq
  have hsum : ∑ y : H, f y = 7 := prime246_quadratic_row x
  simp only [Finset.sum_boole, hsum, Finset.sum_const, Finset.card_univ, card_H] at heq
  have hdiag : Finset.univ.filter (fun y : H => y = x) = {x} := by ext; simp
  rw [hdiag, Finset.card_singleton] at heq
  norm_num only [nsmul_eq_mul] at heq
  change (Finset.univ.filter (fun y : H => f y = 1)).card = 67
  omega

/-- The signed sum on the ordered square of the evaluation subgroup in the
classical Paley graph is exactly 896. -/
theorem prime246_quadratic_sum :
    ∑ x : H, ∑ y : H, quadraticChar K (domain x - domain y) = 896 := by
  simp only [prime246_quadratic_row, Finset.sum_const, Finset.card_univ, card_H]
  norm_num

#print axioms shawGapLaw_one_of_card_le_log
#print axioms prime246_shawGapLaw
#print axioms prime246_large_period
#print axioms prime246_both_prizes_and_spectrum
#print axioms prime246_quadratic_row
#print axioms prime246_induced_degree
#print axioms prime246_quadratic_sum

end ProximityGap.PrizeInstancePaleySpectrum
