/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateDoubleInterpolation
import ArkLib.Research.ProximityGap.Frontier.QuarterRateFreshPairExtension

/-! # The first-prime rate-quarter predecessor and the extended two-head probability -/

namespace ArkLib.ProximityGap.Frontier.QuarterRateTwoRichFloor
open Finset Code HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterComplementaryCores
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Up to one step before saturation the two rich cores cover every bad label. -/
theorem family_cap (fam : BadScalarRichPointFamily dom 268435456 δ u) {e t : ℕ}
    (hn : Fintype.card I = 1073741824) (hsum : e+t = 1073741824)
    (he : 442128987 ≤ e) (hu : e ≤ 447392426)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) :
    fam.G.card ≤ 2*(e+1) := by
  classical
  by_contra! large
  obtain ⟨a,ha,b,hb,hab,h₁,h₂⟩ := QuarterRateDoubleInterpolation.heavy_pair fam hn hsum
    (by change 626349397 ≤ t; omega) ht hchar (by decide : 511 ≤ 150000000) (by omega) (by omega) (by omega)
  let D (a : LineParameter F) := jointCore dom (u 0) (u 1) a.1 a.2
  have near (a : LineParameter F) (ha : a ∈ lineParameters fam) (h : 150000000 < (pointsOn fam a).card) :
      t-2 ≤ (D a).card := by
    have hs := pointsOn_card_mul_max_add_core_le fam ha
    rw [ht,hn] at hs
    change (pointsOn fam a).card * max 1 (t - (D a).card) + (D a).card ≤ _ at hs
    have grow := Nat.mul_le_mul (show 150000001 ≤ (pointsOn fam a).card by omega)
      (Nat.le_max_right 1 (t - (D a).card))
    omega
  have hA := near _ ha h₁
  have hB := near _ hb h₂
  have inter : (D a ∩ D b).card ≤ 268435455 :=
    jointCore_inter_card_le_degree_pred fam (by decide) ha hb hab
  have un := card_union_add_card_inter (D a) (D b)
  have nU := (card_le_univ (D a ∪ D b)).trans_eq hn
  have small : (univ \ (D a ∪ D b)).card + 2*268435455 < t := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn]
    omega
  have cover := G_subset_two_lines_of_small_core_complement fam (by decide) (h:=t-1)
    (by omega) a b ha hb (by simpa only [show t-1+1=t by omega] using small)
  have bounds := (card_le_card cover).trans (card_union_le ..)
  have h1 := TwoLargeCoreCount.line_occupancy_le fam (hn.trans hsum.symm) ht ha
  have h2 := TwoLargeCoreCount.line_occupancy_le fam (hn.trans hsum.symm) ht hb
  omega

/-- The maximal numerator at the saturated step is bounded by the exact two-head count. -/
theorem saturated_exact_cap (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) : fam.G.card ≤ 894784856 := by
  by_contra! large
  obtain ⟨a,ha,b,hb,hab,h₁,h₂⟩ := QuarterRateDoubleInterpolation.asymmetric_heavy_pair fam hn
    (e:=447392427) (by decide) (by decide) ht hchar (by decide : 511 ≤ 150000000)
    (by decide : 150000000 ≤ 223696214) (by omega) (by omega) (by omega)
  exact QuarterRateFreshPairExtension.impossible_asymmetric fam hn ht large ha hb hab h₁ h₂

/-- Compatibility with the upper estimate retaining all sixteen possible vertical exceptions. -/
theorem saturated_cap (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) : fam.G.card ≤ 894784872 :=
  (saturated_exact_cap fam hn ht hchar).trans (by decide)

/-- The exact two-head probability for every supplied injective domain in the range. -/
theorem exact_mass (dom : I ↪ F) (hn : Fintype.card I = 1073741824) {e : ℕ}
    (he : 402653184 ≤ e) (hu : e ≤ 447392426)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) ((e : ℝ≥0) / Fintype.card I)
      = ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  by_cases old : e ≤ 442128987
  · exact QuarterRateQuadraticSafety.exact_mass dom hn he old (fun i hi hj => hchar i hi (by omega))
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let δ : ℝ≥0 := e/Fintype.card I
    let fam := canonicalBadScalarRichPointFamily dom δ u (by decide : 1≤268435456)
    have hc : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 1073741824-e := by
      dsimp only [δ]
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ hc,← Nat.cast_tsub,Nat.ceil_natCast,hn]
    exact family_cap fam hn (by omega) (by omega) hu ht hchar
  · exact TwoHeadLinearBudget.errors dom (by omega) (by omega) (by omega)

/-- The upper and lower constructions match at the saturated predecessor as well. -/
theorem exact_through_saturation (dom : I ↪ F) (hn : Fintype.card I = 1073741824) {e : ℕ}
    (he : 402653184 ≤ e) (hu : e ≤ 447392427)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) ((e : ℝ≥0) / Fintype.card I)
      = ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  by_cases last : e = 447392427
  · subst e
    apply le_antisymm
    · rw [hn]
      apply epsMCA_le_of_badCount_le _ _ 894784856
      intro u
      let fam := canonicalBadScalarRichPointFamily dom (447392427/1073741824) u (by decide : 1 ≤ 268435456)
      apply saturated_exact_cap fam hn _ hchar
      rw [hn]
      change ⌈(1-((447392427 : ℕ) : ℝ≥0)/((1073741824 : ℕ) : ℝ≥0))*((1073741824 : ℕ) : ℝ≥0)⌉₊ = _
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num),← Nat.cast_tsub,Nat.ceil_natCast]
    · exact TwoHeadLinearBudget.errors dom (by omega) (by omega) (by omega)
  · exact exact_mass dom hn he (by omega) hchar

/-- All received pairs meet the previously published upper bound at saturation. -/
theorem saturated_upper (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) (447392427/1073741824) ≤
      (894784872 : ℝ≥0∞)/Fintype.card F := by
  have hp := exact_through_saturation dom hn (by decide : 402653184 ≤ 447392427) (le_refl _) hchar
  rw [hn] at hp
  exact hp.le.trans (ENNReal.div_le_div_right (by norm_num) _)

open ArkLib.ProximityGap.PrizeShapePrimeP30 P1RateQuarterCanonicalCodeBridge P1RateQuarterScaleArithmetic
local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

/-- End-to-end first-prime quarter-rate interval. -/
theorem named_bracket :
    let radius := mcaDeltaStar (F := ZMod P) canonicalCode ((((2^128 : ℕ) : ℝ≥0∞))⁻¹)
    (447392428 : ℝ≥0)/1073741824 ≤ radius ∧ radius ≤ 480946859/1073741824 := by
  dsimp only
  refine ⟨?_,QuarterRateApolarBracket.named_bracket.2⟩
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a:=447392428) (by decide) (by decide : 447392428 ≤ N)
  have upper := saturated_upper canonicalDomain (Fintype.card_fin _) (by
    intro i hi hj hz
    have big : 1968526676 < P := by decide
    exact (lt_of_le_of_lt hj big).not_ge (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod P) P i).mp hz)))
  rw [ZMod.card] at upper
  exact upper.trans (natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) prime_P.pos (by decide))

/-- The field-order budget on a prime field automatically gives the characteristic bound. -/
theorem prime_budget_through_saturation {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I = 1073741824) (hB : p / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 894784857) (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  apply QuarterRateQuadraticSafety.budget_window_of_mass dom hn (by simpa only [ZMod.card] using hB) hl (by omega) _ width
  apply exact_through_saturation dom hn (by omega) (by omega)
  intro i hi hj hz
  exact (show ¬p ≤ i by omega) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp hz))

/-- The field-order budget on a prime field automatically gives the characteristic bound. -/
theorem prime_budget_window {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I = 1073741824) (hB : p / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 894784855) (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r :=
  prime_budget_through_saturation dom hn hB hl (by omega) width

#print axioms exact_through_saturation
#print axioms prime_budget_through_saturation
#print axioms prime_budget_window
#print axioms family_cap
#print axioms saturated_cap
#print axioms exact_mass
#print axioms saturated_upper
#print axioms named_bracket
end ArkLib.ProximityGap.Frontier.QuarterRateTwoRichFloor
