/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier.QuarterRateApolarBracket
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Research.ProximityGap.Frontier.QuadraticTwoHeadCount

/-! # The exact two-head numerator on a length-$2^{30}$ quarter-rate interval

A degree-34 interpolant of value degree two covers every selected witness at
631612837 agreements. A populous irreducible component is necessarily a secant.
Every sufficiently large subfamily therefore supplies a large joint core.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateQuadraticSafety

open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- The actual bad scalar count is at most twice the number of errors plus two throughout
the quarter-rate interval. The domain may be any injection into a field of large characteristic. -/
theorem family_cap (fam : BadScalarRichPointFamily dom 268435456 δ u) {e t : ℕ}
    (hn : Fintype.card I = 1073741824) (hsum : e + t = 1073741824)
    (he : 402653184 ≤ e) (htmin : 631612837 ≤ t)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = t)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0) :
    fam.G.card ≤ 2 * e + 2 := by
  exact QuadraticTwoHeadCount.family_cap (t₀:=631612837) fam hn hsum (by decide) (by decide)
    (by omega) htmin (by decide) ht hchar

/-- The exact worst-case two-row failure mass at every integer error count in the interval. -/
theorem exact_mass (dom : I ↪ F) (hn : Fintype.card I = 1073741824) {e : ℕ}
    (he : 402653184 ≤ e) (hu : e ≤ 442128987)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0) :
    epsMCA (F := F) (ReedSolomon.code dom 268435456 : Set (I → F)) ((e : ℝ≥0) / Fintype.card I)
      = ((2*(e+1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let δ : ℝ≥0 := e / Fintype.card I
    let fam := canonicalBadScalarRichPointFamily dom δ u (by decide : 1 ≤ 268435456)
    change fam.G.card ≤ 2*(e+1)
    have hc : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 1073741824-e := by
      dsimp only [δ]
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ hc, ← Nat.cast_tsub, Nat.ceil_natCast, hn]
    simpa only [Nat.mul_add,Nat.mul_one] using
      family_cap fam hn (t := 1073741824-e) (by omega) he (by omega) ht hchar
  · exact TwoHeadLinearBudget.errors dom (by omega) (by omega) (by omega)

open ArkLib.ProximityGap.PrizeShapePrimeP30 P1RateQuarterCanonicalCodeBridge
open P1RateQuarterScaleArithmetic _root_.ProximityGap.MCAThresholdLedger PrizeShapeRateHalfBracket

local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

/-- The first-prime first bad grid point is between 442128988 and 480946859 inclusive. -/
theorem named_bracket :
    let radius := mcaDeltaStar (F := ZMod P) canonicalCode ((((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹)
    (442128988 : ℝ≥0)/1073741824 ≤ radius ∧ radius ≤ 480946859/1073741824 := by
  dsimp only
  refine ⟨?_, QuarterRateApolarBracket.named_bracket.2⟩
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 442128988)
    (by decide) (by decide : 442128988 ≤ N)
  change epsMCA (F := ZMod P) canonicalCode ((442128987 : ℝ≥0) / N) ≤ _
  have mass := exact_mass canonicalDomain (Fintype.card_fin _) (e := 442128987)
    (by decide) (by decide) (by
      intro i hi hj hc
      have hP : 1263225672 < P := by decide
      exact (lt_of_le_of_lt hj hP).not_ge
        (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod P) P i).mp hc)))

  rw [Fintype.card_fin, ZMod.card] at mass
  exact mass.le.trans (natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide) prime_P.pos (by decide))

/-- An exact two-head predecessor mass, together with the next two-head
construction, determines the operational crossing on all positive widths. -/
theorem budget_window_of_mass (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 1073741821)
    (previous : epsMCA (F:=F) (ReedSolomon.code dom 268435456 : Set (I → F))
      (((B/2-1 : ℕ) : ℝ≥0)/Fintype.card I) = ((2*((B/2-1)+1) : ℕ) : ℝ≥0∞)/Fintype.card F)
    (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  classical
  let e := B/2
  let r : ℝ≥0 := (e : ℝ≥0)/1073741824
  let r₀ : ℝ≥0 := ((e-1 : ℕ) : ℝ≥0)/1073741824
  let C := (ReedSolomon.code dom 268435456 : Set (I → F))
  have hlo : 402653185 ≤ e := by dsimp [e]; omega
  have hhi : e ≤ 536870910 := by dsimp [e]; omega
  have ratio (m : ℕ) :
      ((m : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (epsStar : ℝ≥0∞)) ↔ m ≤ B := by
    rw [epsStar_coe_eq_natCast_inv, ← one_div, ← hB]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide)
  have good : epsMCA (F := F) C r₀ ≤ (epsStar : ℝ≥0∞) := by
    rw [hn] at previous
    apply previous.le.trans
    apply (ratio _).2
    omega
  have bad : (epsStar : ℝ≥0∞) < epsMCA (F := F) C r := by
    have h := TwoHeadLinearBudget.errors (k := 268435456) (e := e) dom (by omega) (by omega) (by omega)
    rw [hn] at h
    apply lt_of_lt_of_le _ h
    apply lt_of_not_ge
    rw [ratio]
    dsimp [e]
    omega
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) 268435456
  have radius : mcaDeltaStar (F := F) C (epsStar : ℝ≥0∞) = r := by
    dsimp only [C]
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a := e)
      (by omega) (by omega)
    · rw [← hre]
      exact good
    · rw [← hre]
      exact bad
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact radius, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! hδ
    exact bad.not_ge ((epsMCA_mono C hδ).trans safe)
  · intro hδ
    by_contra! unsafeAt
    have bound := mcaDeltaStar_le_of_bad C (epsStar : ℝ≥0∞) unsafeAt
    rw [radius] at bound
    exact hδ.not_ge bound

/-- Across this interval of integer 128-bit budgets every positive-width MCA test
passes precisely below the grid point picked by half the budget. -/
theorem budget_window (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    {B : ℕ} (hB : Fintype.card F / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 884257977)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1263225672 → (i : F) ≠ 0)
    (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom 268435456 : Set (I → F)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  apply budget_window_of_mass dom hn hB hl (by omega) _ width
  exact exact_mass dom hn (by omega) (by omega) hchar

/-- The field-order budget on a prime field automatically gives the characteristic bound. -/
theorem prime_budget_window {p B : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I = 1073741824) (hB : p / 2^128 = B)
    (hl : 805306370 ≤ B) (hu : B ≤ 884257977) (width : ℕ) [NeZero width] :
    let r : ℝ≥0 := ((B/2 : ℕ) : ℝ≥0)/1073741824
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      (epsStar : ℝ≥0∞) = r ∧
    ∀ δ : ℝ≥0, epsMCA (F := ZMod p) ((ReedSolomon.code dom 268435456 : Set (I → ZMod p)) ^⋈ (Fin width))
      δ ≤ (epsStar : ℝ≥0∞) ↔ δ < r := by
  apply budget_window dom hn (by simpa only [ZMod.card] using hB) hl hu _ width
  intro i hi hj hz
  exact (show ¬p ≤ i by omega) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff (ZMod p) p i).mp hz))

#print axioms budget_window
#print axioms prime_budget_window

#print axioms family_cap
#print axioms exact_mass
#print axioms named_bracket

end ArkLib.ProximityGap.Frontier.QuarterRateQuadraticSafety
