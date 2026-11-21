/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralManyLineSafety
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Three affine heads at the two-thirds error boundary

At length 2^30 the same first failure holds throughout an explicit low-dimension
interval, on every injective evaluation domain over a field in the stated
budget class. The cubic moment and three-core inequality use a line occupancy
cut of 27 at both adjacent error counts.
-/

set_option autoImplicit false
namespace ProximityGap.LowDimensionThreeLinePhase
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket MCAThresholdLedger
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The exact number of worst-pair bad labels at either side of the threshold,
over every finite field large enough to project all private-core keys. -/
theorem adjacent_mass (x : Fin 1073741824 ↪ F) {k e : ℕ}
    (low : 3≤k) (high : k≤39768172) (first : 715827881≤e) (last : e≤715827882)
    (room : 2305843010287435776≤Fintype.card F) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin 1073741824 → F)) ((e:ℝ≥0)/1073741824) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  apply GeneralManyLineSafety.epsMCA_eq_of_pair_supply (r:=3) (L:=27) (t:=1073741824-e) x _
    (by omega) (by omega) (by omega) (by decide) (by decide)
  · simp only [Nat.cast_ofNat]
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num)]
    have ne : ((1073741824:ℕ):ℝ≥0)=1073741824 := by norm_num
    rw [←ne,←Nat.cast_tsub,Nat.ceil_natCast]
  · interval_cases e <;> norm_num at * <;> omega
  · norm_num
    omega
  · omega
  · apply (Nat.choose_le_choose 2 (by omega : 3*(e+1)≤2147483649)).trans
    rwa [Nat.choose_two_right]

/-- At the 128-bit tolerance and a budget of twice the block length, the first
failing error count is exactly 715827882 and every smaller radius is good. -/
theorem classification (x : Fin 1073741824 ↪ F) {k : ℕ} (low : 3≤k) (high : k≤39768172)
    (budget : Fintype.card F/2^128=2147483648) :
    let C := (ReedSolomon.code x k : Set (Fin 1073741824 → F))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := (715827882:ℝ≥0)/1073741824
    mcaDeltaStar (F:=F) C ε=b ∧ ∀ δ, epsMCA (F:=F) C δ≤ε ↔ δ<b := by
  dsimp only
  have room : 2305843010287435776≤Fintype.card F := by omega
  have prev := adjacent_mass x low high (e:=715827881) (by decide) (by decide) room
  have cur := adjacent_mass x low high (e:=715827882) (by decide) (by decide) room
  simp only [Nat.cast_ofNat] at prev cur
  have cnt (a : ℕ) := BoundarySecurityBudget.count_ratio_le_iff (a:=a) (q:=Fintype.card F) Fintype.card_pos (by decide : 0<2^128)
  have good : epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin 1073741824 → F))
      (predecessorRadius 1073741824 715827882)≤1/(2:ℝ≥0∞)^128 := by
    unfold predecessorRadius
    rw [show 715827882-1=715827881 by decide]
    simp only [Nat.cast_ofNat]
    rw [prev]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (cnt (3*(715827881+1))).2 (by omega)
  have bad : 1/(2:ℝ≥0∞)^128 < epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin 1073741824 → F))
      ((715827882:ℝ≥0)/1073741824) := by
    rw [cur]
    apply lt_of_not_ge
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      (mt (cnt (3*(715827882+1))).1 (by omega))
  have pin := le_antisymm (mcaDeltaStar_le_of_bad _ _ bad)
    (latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by decide) (by decide) _ _ good)
  refine ⟨pin,fun δ => ⟨fun h => ?_,fun h => ?_⟩⟩
  · by_contra! hb
    exact bad.not_ge ((epsMCA_mono _ hb).trans h)
  · by_contra! hbad
    exact h.not_ge (pin ▸ mcaDeltaStar_le_of_bad _ _ hbad)

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- In particular the classification applies to every evaluation embedding in
the repository's second certified prime, including its explicit smooth domain. -/
theorem second_prime (x : Fin 1073741824 ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
    {k : ℕ} (low : 3≤k) (high : k≤39768172) :
    let C := (ReedSolomon.code x k : Set (Fin 1073741824 → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P))
    let ε := 1/(2:ℝ≥0∞)^128
    let b := (715827882:ℝ≥0)/1073741824
    mcaDeltaStar (F:=ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) C ε=b ∧
      ∀ δ, epsMCA (F:=ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) C δ≤ε ↔ δ<b := by
  exact classification x low high (by rw [ZMod.card]; exact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P_div_two_pow_128)

end ProximityGap.LowDimensionThreeLinePhase
#print axioms ProximityGap.LowDimensionThreeLinePhase.adjacent_mass
#print axioms ProximityGap.LowDimensionThreeLinePhase.classification
#print axioms ProximityGap.LowDimensionThreeLinePhase.second_prime
