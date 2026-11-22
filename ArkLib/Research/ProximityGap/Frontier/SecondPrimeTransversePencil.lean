/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeTransverseAllocation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeTransverseEvents
import ArkLib.Research.ProximityGap.Frontier.QuarterTransverseKeys
import ArkLib.Research.ProximityGap.SecondPrimeJohnsonPivot

/-! # A split pencil would force the second-prime quarter-rate MCA supremum below Johnson

The zero, pole and unit fibers of the pencil give three large joint cores. A
fourth head agrees with the received pair on the zero fiber and on every free
site. Together the four heads yield two more labels than the production budget.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeTransversePencil

open Finset Polynomial Code _root_.ProximityGap SmoothFourHeadColored
open QuarterSuccessorSplitCriterion _root_.ProximityGap.QuarterTransverseKeys
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

/-- A split pencil on the supplied domain gives 2,147,483,650 literal MCA-bad
scalars for one received pair at the quarter-rate Johnson pivot. -/
theorem actual_events (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (room : 2147483650 ^ 2 < Fintype.card F) (pencil : splitPencil D) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F), G.card = 2147483650 ∧
      ∀ z ∈ G, mcaEvent (ReedSolomon.code D 268435456 : Set (I → F))
        (536870913 / 1073741824) (u 0) (u 1) z := by
  classical
  obtain ⟨col, f, counts, deg, zero, fiber, agree, misses, free⟩ :=
    SecondPrimeTransverseAllocation.allocation D hn pencil
  let P := f 1
  let v (j : Fin 3) (x : I) := (f j).eval (D x) / P.eval (D x)
  have inj (x : I) (hx : col x = 7) : Function.Injective (fun j => v j x) := by
    have hp : P.eval (D x) ≠ 0 := fun h =>
      (by decide : (7 : Fin 8) ≠ 2) (hx.symm.trans ((fiber x).mpr h))
    exact fun _ _ eq => free x hx ((div_left_inj' hp).mp eq)
  let select (s : Finset (Fin 8)) := univ.filter fun x => col x ∈ s
  have scard (s : Finset (Fin 8)) :
      (select s).card = ∑ j ∈ s, weight 268435454 0 2 268435456 j := by
    rw [← sum_card_fiberwise_eq_card_filter univ s col]
    exact sum_congr rfl (fun j _ => counts j)
  have orig (j : Fin 3) : (select (coreClasses j)).card = 536870910 := by
    rw [scard]
    fin_cases j <;> norm_num [coreClasses, weight, Finset.sum_insert]
  have fourth : (univ.filter fun x => col x = 2 ∨ col x = 7).card = 536870910 := by
    convert scard {2, 7} using 1
    · simp [select]
    · norm_num [weight, Finset.sum_insert]
  have size : _root_.ProximityGap.QuarterTransverseKeys.mass col = 2147483650 := by
    have ordinaryCount := scard ordinaryClasses
    have variableCount := scard (ordinaryClasses.erase 2)
    have hvar : variableSites col = select (ordinaryClasses.erase 2) := by
      ext x
      simp [variableSites, select, and_comm]
    rw [_root_.ProximityGap.QuarterTransverseKeys.mass, hvar, variableCount]
    change (select ordinaryClasses).card + _ + 3 * (univ.filter fun x => col x = 7).card = _
    rw [ordinaryCount, counts, show ordinaryClasses.erase 2 = {0, 1, 4, 5, 6} by decide]
    norm_num [weight, ordinaryClasses, Finset.sum_insert]
  obtain ⟨a, c, G, avoid, hG, labels⟩ := exists_labels D col v inj
    (by rw [hn]; omega) (by simpa only [size] using room)
  have threshold : (1 - 536870913 / 1073741824 : ℝ≥0) * Fintype.card I ≤
      ((536870910 + 1 : ℕ) : ℝ≥0) := by
    rw [hn, Nat.cast_ofNat, tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num)]
    norm_num [tsub_le_iff_right]
  obtain ⟨u, fixed, extra, hole⟩ := SecondPrimeTransverseEvents.events D 268435456
    (536870913 / 1073741824) col f a c (fun j => by have := deg j; omega) zero fiber
    agree misses avoid (fun j => by
      change _ ≤ (select (coreClasses j)).card
      rw [orig]; decide)
    (fun j => by change _ ≤ (((select (coreClasses j)).card + 1 : ℕ) : ℝ≥0); rwa [orig])
    (by rw [fourth]; decide) (by rwa [fourth])
  have hit (z : F) (hz : z ∈ G) :
      mcaEvent (ReedSolomon.code D 268435456 : Set (I → F)) (536870913 / 1073741824)
        (u 0) (u 1) z := by
    rcases labels z hz with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ | ⟨x,hx,j,rfl⟩
    · exact fixed x (mem_filter.mp hx).2
    · exact extra x (mem_filter.mp hx).2.1 (mem_filter.mp hx).2.2
    · exact hole x (mem_filter.mp hx).2 j
  exact ⟨u, G, hG.trans size, hit⟩

/-- Probability lower bound from the simultaneous set of bad scalars. -/
theorem mass (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (room : 2147483650 ^ 2 < Fintype.card F) (pencil : splitPencil D) :
    (2147483650 : ℝ≥0∞) / Fintype.card F ≤
      epsMCA (F := F) (ReedSolomon.code D 268435456 : Set (I → F)) (536870913 / 1073741824) := by
  classical
  obtain ⟨u, G, hG, hit⟩ := actual_events D hn room pencil
  have bound := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ _ u G hit
  simpa only [hG, Nat.cast_ofNat] using bound

open SecondPrimeSmoothSeed (N dom)
open PrizeShapePrimeP30Second (P prime_P)
open _root_.ProximityPrize
local instance : Fact P.Prime := ⟨prime_P⟩

/-- On the actual second-prime subgroup, any such pencil decides the strict
comparison for the unrestricted MCA error and every positive interleaving width. -/
theorem quarter_below_of_split (pencil : splitPencil dom) (width : ℕ) [NeZero width] :
    (MCAThresholdLedger.mcaDeltaStar (F := SecondPrimeSmoothSeed.F)
      ((ReedSolomon.code dom (2 ^ 28) : Set (Fin N → SecondPrimeSmoothSeed.F)) ^⋈ (Fin width))
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) : ℝ) < DesignatedPrimeJohnson.johnson (2 ^ 28) := by
  apply (SecondPrimeJohnsonPivot.quarter width).2.1.mp
  rw [epsMCA_interleaved_eq]
  have bound := mass dom (by simp [N]) (by rw [ZMod.card]; decide) pencil
  apply lt_of_lt_of_le _ bound
  rw [ZMod.card]
  have high : (prizeThreshold : ℝ≥0) < (2147483650 : ℝ≥0) / P := by
    apply (lt_div_iff₀ (show (0 : ℝ≥0) < (P : ℝ≥0) by exact_mod_cast prime_P.pos)).mpr
    exact_mod_cast (show (prizeThreshold : ℝ) * (P : ℝ) < 2147483650 by
      norm_num [prizeThreshold, PrizeShapePrimeP30Second.P])
  have hp : (P : ℝ≥0) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  simpa only [ENNReal.coe_div hp, ENNReal.coe_ofNat, ENNReal.coe_natCast] using
    ENNReal.coe_lt_coe.mpr high

end ArkLib.ProximityGap.Frontier.SecondPrimeTransversePencil
