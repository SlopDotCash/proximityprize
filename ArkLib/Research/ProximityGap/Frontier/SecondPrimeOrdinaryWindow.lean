/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeTerminalCharge
import ArkLib.Research.ProximityGap.Frontier.TerminalCubicBudgetWindow

/-! # The cubic budget interval using ordinary polars on a common coordinate chart -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryWindow
open Polynomial Finset Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity SecondPrimeActualPopulations SecondPrimeCoordinateWeight
open MovingCubicVanishingBranch CanonicalQuarticSiteOrder SecondPrimeScalarChart
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

variable {F I K : Type} [Fintype I] [Nonempty I] [Field F] [DecidableEq F] [Field K]
  [Infinite K] {p : ℕ} [CharP K p] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- All supported cubic components fall below the least population forced at any radius
in the terminal interval. The low-weight case uses a common chart for the received rows. -/
theorem cubic_cap (fam : Family dom δ u) (φ : F →+* K) (hp : 1320000000 < p)
    (hn : Fintype.card I = n) (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (Q f : K[X][X][X]) (hQ : Q ≠ 0) (hi : Irreducible f) (hd : f ∣ Q) (hf : f.natDegree = 3)
    (shape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34) :
    (population fam φ f).card < 1342177249 := by
  classical
  by_cases hw : weight 67108863 f < 220000000
  · exact SecondPrimeTerminalCharge.population_cap fam φ hp hn ht Q f hQ hi hd hf shape hw
  by_cases h : genericEquation (scalarChart f) ∣
      genericEquation (scalarFieldHessian (scalarChart f))
  · have cap := SecondPrimeReverseChart.divisible_label_cap φ (p := p)
      ((by decide : 276 ≤ 1320000000).trans_lt hp) f hi (by omega) (by omega)
      (SecondPrimeSectionResultant.factor_triangle hQ hd shape) h (population fam φ f)
      (fun z => (fam.q z).map φ) (fun _ hz => (mem_filter.mp hz).2)
    exact cap.trans_lt (by decide)
  have cap := SecondPrimeActualCubicCap.population_cap fam φ hn ht Q f hQ hd hi hf shape
    (Nat.le_of_not_gt hw) h
  exact cap.trans_lt (by decide)

/-- Every received pair has at most three times the successor error count in bad labels. -/
theorem family_cap [Finite F] (D : I ↪ F) (hn : Fintype.card I = n) {p e : ℕ} [CharP F p]
    (hp : 1320000000 < p) (hl : 671088640 ≤ e) (hu : e ≤ 715827881)
    (δ : ℝ≥0) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = n - e)
    (u : WordStack F (Fin 2) I) (fam : Family D δ u) : fam.G.card ≤ 3 * (e + 1) := by
  classical
  let _ := Fintype.ofFinite F
  by_contra! hlarge
  let φ := algebraMap F (AlgebraicClosure F)
  let _ : CharP (AlgebraicClosure F) p := charP_of_injective_ringHom φ.injective p
  obtain ⟨Q, f, hQ, hs, hi, hd, hf, hpop, _, _⟩ :=
    TerminalCubicBudgetWindow.actual_cubic fam φ ((by decide : 715827884 ≤ 1320000000).trans_lt hp)
      hn hl hu ht hlarge
  exact (cubic_cap fam φ hp hn (by rw [ht]; unfold n; omega) Q f hQ hi hd hf
    (fun j i a ha => (hs j i a ha).2.1)).not_ge hpop

omit [DecidableEq F] in
/-- Exact cutoff for every positive width and all integer field budgets in the terminal
interval over fields of characteristic above 1,320,000,000. -/
theorem classification [Fintype F] (D : I ↪ F) (hn : Fintype.card I = n) {p B : ℕ} [CharP F p]
    (hp : 1320000000 < p) (hB : Fintype.card F / 2 ^ 128 = B)
    (hl : 2013265923 ≤ B) (hu : B ≤ 2147483648) (m : ℕ) [NeZero m] :
    let t : ℝ≥0 := ((B / 3 : ℕ) : ℝ≥0) / n
    mcaDeltaStar (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) tolerance = t ∧
      ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤
        tolerance ↔ δ < t := by
  classical
  apply TerminalCubicBudgetWindow.classification_of_family_bound D hn hB hl hu _ m
  intro u
  let fam := canonicalBadScalarRichPointFamily D (k := k)
    (((B / 3 - 1 : ℕ) : ℝ≥0) / n) u (by decide)
  apply family_cap D hn hp (by omega) (by omega) _ _ u fam
  rw [hn]
  have h := TwoCorePackingThreshold.agreement_ceiling (B / 3 - 1)
    (by change B / 3 - 1 ≤ 1073741824; omega)
  rw [Fintype.card_fin] at h
  exact h

#print axioms classification
end ArkLib.ProximityGap.Frontier.SecondPrimeOrdinaryWindow
