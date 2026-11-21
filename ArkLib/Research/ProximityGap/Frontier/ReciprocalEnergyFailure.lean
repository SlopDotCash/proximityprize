/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalChartMoments
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMcaLift

/-! # Low additive energy alongside failure of 128-bit MCA

A single reciprocal chart of the smooth 246-bit prime field construction
has factorially bounded order-four energy and still fails simultaneously at
the four previously certified radii.
-/

set_option autoImplicit false

namespace ProximityGap.ReciprocalEnergyFailure
open Finset ReciprocalChartMCA FourRateSmoothMcaLift
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

private theorem compare (C C' : Set (I → F)) (δ : ℝ≥0)
    (h : ∀ u : Code.WordStack F (Fin 2) I, ∃ v : Code.WordStack F (Fin 2) I, ∀ z : F,
      mcaEvent (F:=F) C δ (u 0) (u 1) z → mcaEvent (F:=F) C' δ (v 0) (v 1) z) :
    epsMCA (F:=F) C δ ≤ epsMCA (F:=F) C' δ := by
  classical
  rw [epsMCA_eq_iSup_badCount_div,epsMCA_eq_iSup_badCount_div]
  apply ENNReal.div_le_div_right _ _
  apply iSup_le
  intro u
  obtain ⟨v,hv⟩ := h u
  apply le_iSup_of_le v
  apply Nat.cast_le.mpr
  apply card_le_card
  intro z hz
  exact mem_filter.mpr ⟨mem_univ _,hv z (mem_filter.mp hz).2⟩

/-- Worst-case MCA error agrees exactly on the two coordinate systems. -/
theorem eps_eq (x : I ↪ F) (t : F) (ht : ∀ i, t≠x i) (D : ℕ) (δ : ℝ≥0) :
    epsMCA (F:=F) (ReedSolomon.code x (D+1) : Set (I → F)) δ =
    epsMCA (F:=F) (ReedSolomon.code (chart x t) (D+1) : Set (I → F)) δ := by
  apply le_antisymm
  · apply compare
    intro u
    exact ⟨fun j i => (chart x t i)^D * u j i,fun z => (event_iff x t ht D δ _ _ z).mp⟩
  · apply compare
    intro u
    let v : Code.WordStack F (Fin 2) I := fun j i => ((chart x t i)^D)⁻¹ * u j i
    have clean (j : Fin 2) : (fun i => (chart x t i)^D * v j i) = u j := by
      funext i
      have hn : chart x t i ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (ht i))
      simp [v,pow_ne_zero D hn]
    refine ⟨v,fun z hz => (event_iff x t ht D δ _ _ z).mpr ?_⟩
    rwa [clean,clean]

/-- There is an explicit field and an injective length-2³⁰ domain with
order-four energy at most 24n⁴ on which all four known bad radii remain bad.
The starting domain is smooth. Its reciprocal chart may lose smoothness. -/
theorem prime246_four_failures :
    ∃ y : Fin (2^30) ↪ FourRateListPrime246.K,
      rEnergy (univ.map y) 4 ≤ (2^30)^4*24 ∧
      ∀ j : Fin 4, ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
        epsMCA (F:=FourRateListPrime246.K)
          (ReedSolomon.code y (prizeDimension (ι:=Fin (2^30)) j) : Set (Fin (2^30) → FourRateListPrime246.K)) (failureRadius j) := by
  classical
  obtain ⟨x,⟨hx⟩⟩ := SmoothPowerMcaDescent.exists_prime_domain
    (p:=FourRateListPrime246.P) (n:=2^30) (by decide) ⟨30,rfl⟩
  let := hx
  obtain ⟨t,ht,energy⟩ := ReciprocalChartMoments.prime_energy x 4 (by decide) (by
    rw [Fintype.card_fin]
    decide)
  refine ⟨chart x t,by simpa only [Fintype.card_fin,show Nat.factorial 4 = 24 by decide] using energy,fun j => ?_⟩
  have fail := all_rates_bad x (r:=2097152) (by decide) (by rw [Fintype.card_fin]; decide)
    FourRateSmoothMca128.prime246_window j (failureRadius j) le_rfl
  have pos : 0 < prizeDimension (ι:=Fin (2^30)) j := by
    unfold prizeDimension
    rw [Fintype.card_fin]
    fin_cases j <;> decide
  obtain ⟨D,e⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  rw [e] at fail ⊢
  simpa only [← eps_eq x t ht D] using fail

end ProximityGap.ReciprocalEnergyFailure
#print axioms ProximityGap.ReciprocalEnergyFailure.eps_eq
#print axioms ProximityGap.ReciprocalEnergyFailure.prime246_four_failures
