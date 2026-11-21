/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmoothSeed
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # Four-head error ceilings on the second designated prime

The three cubic fibers on the production power domain admit disjoint private
allocations. The same four defining cores certify bad labels at every code
dimension between the intended rate and their common core size.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeFourHeadEndpoints
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed ArkLib.ProximityGap.PrizeShapePrimeP30Second

local instance : Fact P.Prime := ⟨prime_P⟩

/-- The power-of-two tolerance used in the production challenge. -/
abbrev tolerance : ℝ≥0∞ := 1/(2:ℝ≥0∞)^128

private theorem over_budget {rows : ℕ} (hr : 2147483648 < rows) :
    tolerance < (rows:ℝ≥0∞)/(P:ℝ≥0∞) := by
  by_contra! h
  have hc := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos (by decide : 0<2^128)).1
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h : (rows:ℝ≥0∞)/P≤1/((2^128:ℕ):ℝ≥0∞))
  exact hr.not_ge (hc.trans (by decide))

/-- At the eighth-rate endpoint there is a simultaneous four-head stack with at least
2,239,758,344 bad labels, throughout this dimension interval and at each positive width. -/
theorem eighth_mass {k : ℕ} (hl : 134217728 ≤ k) (hu : k ≤ 394264574)
    (width : ℕ) [NeZero width] :
    (2239758344:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (679477249/1073741824) := by
  rw [epsMCA_interleaved_eq]
  have hmain := SmoothFourHeadFibers.mass dom (679477249/1073741824) k
    100663296 33554430 159383552 260046850 134217726 2
    (fun x => bucket 2 (x.val%32)) (seed 33554432) eighth.1 (degree 33554432) eighth.2
    (by omega) (by omega) (by decide) (by decide) (by omega) (by decide) (by
      rw [Fintype.card_fin, tsub_mul, one_mul]
      norm_num [N, tsub_le_iff_right])
    (by rw [Fintype.card_fin, ZMod.card]; decide) (by rw [ZMod.card]; decide)
    (by rw [Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right]; decide)
  rw [show 3*100663296+3*159383552+(33554430+3*100663296+3*159383552-134217726)+
      3*(260046850-2)+4*2=2239758344 by decide, ZMod.card] at hmain
  simpa only [Nat.cast_ofNat] using hmain

/-- The original MCA test fails at the eighth-rate four-head error count. -/
theorem eighth_bad (width : ℕ) [NeZero width] :
    tolerance < epsMCA (F:=F) ((ReedSolomon.code dom 134217728 : Set (Fin N → F)) ^⋈ (Fin width))
      (679477249/1073741824) :=
  (over_budget (by decide : 2147483648 < 2239758344)).trans_le (eighth_mass le_rfl (by decide) width)

/-- At the quarter-rate endpoint there is a simultaneous four-head stack with at least
2,147,483,651 bad labels, throughout this dimension interval and at each positive width. -/
theorem quarter_mass {k : ℕ} (hl : 268435456 ≤ k) (hu : k ≤ 508109969)
    (width : ℕ) [NeZero width] :
    (2147483651:ℝ≥0∞)/(P:ℝ≥0∞) ≤
      epsMCA (F:=F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) (565631854/1073741824) := by
  rw [epsMCA_interleaved_eq]
  have hmain := SmoothFourHeadFibers.mass dom (565631854/1073741824) k
    201326592 67108862 38347923 287609417 268435454 47934902
    (fun x => bucket 1 (x.val%16)) (seed 67108864) quarter.1 (degree 67108864) quarter.2
    (by omega) (by omega) (by decide) (by decide) (by omega) (by decide) (by
      rw [Fintype.card_fin, tsub_mul, one_mul]
      norm_num [N, tsub_le_iff_right])
    (by rw [Fintype.card_fin, ZMod.card]; decide) (by rw [ZMod.card]; decide)
    (by rw [Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right]; decide)
  rw [show 3*201326592+3*38347923+(67108862+3*201326592+3*38347923-268435454)+
      3*(287609417-47934902)+4*47934902=2147483651 by decide, ZMod.card] at hmain
  simpa only [Nat.cast_ofNat] using hmain

/-- The original MCA test fails at the quarter-rate four-head error count. -/
theorem quarter_bad (width : ℕ) [NeZero width] :
    tolerance < epsMCA (F:=F) ((ReedSolomon.code dom 268435456 : Set (Fin N → F)) ^⋈ (Fin width))
      (565631854/1073741824) :=
  (over_budget (by decide : 2147483648 < 2147483651)).trans_le (quarter_mass le_rfl (by decide) width)

/-- Operational ceilings at both rates, for every positive interleaving width. -/
theorem ceilings (width : ℕ) [NeZero width] :
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom 134217728 : Set (Fin N → F)) ^⋈ (Fin width)) tolerance
      ≤ 679477249/1073741824 ∧
    mcaDeltaStar (F:=F) ((ReedSolomon.code dom 268435456 : Set (Fin N → F)) ^⋈ (Fin width)) tolerance
      ≤ 565631854/1073741824 :=
  ⟨mcaDeltaStar_le_of_bad _ _ (eighth_bad width), mcaDeltaStar_le_of_bad _ _ (quarter_bad width)⟩

#print axioms eighth_mass
#print axioms quarter_mass
#print axioms ceilings
end ArkLib.ProximityGap.Frontier.SecondPrimeFourHeadEndpoints
