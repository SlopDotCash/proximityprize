/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ActualTerminalQuartic
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier.TerminalFactorCoverage

/-! # The only remaining terminal obstruction is an actual populated cubic -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Code
open scoped NNReal ENNReal
open ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge SecondPrimeActualPopulations
namespace ProximityGap.SecondPrimeCubicOnly

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F] [Field K]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Finite characteristics larger than the discriminant bound have a single
remaining factor type. Its sections are those of the original entire family. -/
theorem actual_cubic (fam : Family dom δ u) (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 715827884 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 357913943) (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧ TerminalFactorCoverage.Supported Q ∧
      ∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧
        1431655733 ≤ (population fam φ f).card ∧ SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098 := by
  classical
  obtain ⟨Q,hQ,hs,f,hi,hd,hh⟩ :=
    SecondPrimeQuadraticFactor.actual_cubic_or_quartic fam φ hp hn ht hbig
  refine ⟨Q,hQ,hs,f,hi,hd,?_⟩
  rcases hh with ⟨hy,hpop,_⟩ | hc
  · have h := ActualTerminalQuartic.actual_quartic_label_cap φ (p := p) (by omega) dom δ u
      hn ht.ge fam Q f hQ hd hi hy (fun j i a he => (hs j i a he).2.1) (population fam φ f)
      (Finset.filter_subset _ _) (fun z hz => (Finset.mem_filter.mp hz).2)
    omega
  · exact hc

open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open TerminalCollinearHeadCount

private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- Excluding just the exhibited terminal cubic closes the named exact MCA
threshold. The matching security failure at the successor is already verified. -/
theorem secondPrime_threshold_of_cubic_exclusion
    (h : ∀ u : WordStack (ZMod p) (Fin 2) (Fin (2^30)),
      let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
        ((715827881 : ℝ≥0)/1073741824) u (by decide)
      let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
      ∀ Q f : Factor (AlgebraicClosure (ZMod p)), Q ≠ 0 → TerminalFactorCoverage.Supported Q →
        Irreducible f → f ∣ Q → f.natDegree = 3 →
        SecondPrimeCoordinateWeight.weight 67108863 f ≤ 290805098 →
        (population fam φ f).card < 1431655733) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (evalCode g (2^30) (2^26-1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0)/1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hN
  have hbig : 2147483648 < fam.G.card := by have hh := Finset.card_le_card hG; omega
  have ht : ⌈(1-(715827881 : ℝ≥0)/1073741824) * (Fintype.card (Fin (2^30)) : ℝ≥0)⌉₊ =
      357913943 := TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
  obtain ⟨Q,hQ,hs,f,hi,hd,hy,hp',hw⟩ :=
    actual_cubic fam (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (p := p) (by decide)
      (Fintype.card_fin _) ht hbig
  exact False.elim ((h u Q f hQ hs hi hd hy hw).not_ge hp')

end ProximityGap.SecondPrimeCubicOnly

open ProximityGap.SecondPrimeCubicOnly in
#print axioms actual_cubic
open ProximityGap.SecondPrimeCubicOnly in
#print axioms secondPrime_threshold_of_cubic_exclusion
