/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothHyperbolaGrid
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Six heads on a hyperbola at the second production prime -/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeHyperbolaGrid
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed (F N dom)
open PrizeShapePrimeP30Second (P prime_P orderOf_g)
local instance : Fact P.Prime := ⟨prime_P⟩

/-- One received stack exceeds the second-prime budget at every dimension in this
interval, including half rate, and every positive interleaving width. -/
theorem label_mass {k : ℕ} (hk : 536870912 ≤ k) (hc : k ≤ 671088638) (width : ℕ) [NeZero width] :
    (2415919114:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (402653185/1073741824) := by
  have hm := SmoothHyperbolaGrid.mass (F := F) (s := 67108864) (by decide) dom 1
    PrizeShapePrimeP30Second.g one_ne_zero orderOf_g (fun i => (one_mul _).symm)
    hk hc (by rw [Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right]; decide) width
  simpa only [ZMod.card, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] using hm

/-- Strict failure at 402,653,185 errors and the resulting operational upper bound. -/
theorem half (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 536870912 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128
    tol < epsMCA (F:=F) code (402653185/1073741824) ∧
      mcaDeltaStar (F:=F) code tol ≤ 402653185/1073741824 := by
  dsimp only
  have hb : 1/(2:ℝ≥0∞)^128 < (2415919114:ℝ≥0∞)/(P:ℝ≥0∞) := by
    by_contra! h
    have hh := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).mp
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : ((2415919114:ℕ):ℝ≥0∞)/P ≤ 1/((2^128:ℕ):ℝ≥0∞))
    exact (by decide : ¬ 2415919114 ≤ P/2^128) hh
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad,mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms label_mass
#print axioms half
end ArkLib.ProximityGap.Frontier.SecondPrimeHyperbolaGrid
