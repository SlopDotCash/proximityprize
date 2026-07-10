/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLargeCoreCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentJensen
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenthArithmeticBridge

/-!
# Assembly of the rate-1/16 half-predecessor incidence proof

This file composes the selected bad-scalar rich-point family, canonical secant lines, the
large-core collapse, the four-point line bound, the unordered weighted-triple upper bound, the
exact incidence identity, discrete Jensen, and the strict numeric separation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal BigOperators Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentJensen
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Full agreements of the selected polynomial above each scalar. -/
noncomputable def selectedAgreements
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (gamma : F) : Finset ι :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma)

/-- Incidence relation between canonical polynomial lines and selected scalar points. -/
def onFamilyLine
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (gamma : F) : Prop :=
  gamma ∈ pointsOn family line

/-- The common-coordinate weight of an unordered selected triple. -/
noncomputable def tripleWeight
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (T : Finset F) : ℕ :=
  (commonCoordinates (selectedAgreements family) T).card

/-- Number of selected agreement sets through a coordinate. -/
noncomputable def incidenceMultiplicity
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (i : ι) : ℕ :=
  (family.G.filter fun gamma => i ∈ selectedAgreements family gamma).card

/-- The abstract line-point finset is the canonical `pointsOn` finset. -/
theorem linePoints_eq_pointsOn
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (line : LineParameter F) :
    linePoints family.G (onFamilyLine family) line = pointsOn family line := by
  ext gamma
  simp [linePoints, onFamilyLine, mem_pointsOn_iff]

/-- Common coordinates of an explicit three-set are its triple agreement intersection. -/
theorem commonCoordinates_three
    (A : F → Finset ι) (x y z : F) :
    commonCoordinates A {x, y, z} = (A x ∩ A y) ∩ A z := by
  ext i
  simp [commonCoordinates]

/-- Elementary total-incidence double count. -/
theorem sum_incidenceMultiplicity_eq_sum_agreement_card
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    ∑ i, incidenceMultiplicity family i =
      ∑ gamma ∈ family.G, (selectedAgreements family gamma).card := by
  classical
  simp only [incidenceMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gamma _hgamma
  simp

/-- Richness gives the total incidence required by Jensen when the threshold is `h+1`. -/
theorem total_incidence_lower
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1) :
    family.G.card * (h + 1) ≤ ∑ i, incidenceMultiplicity family i := by
  rw [sum_incidenceMultiplicity_eq_sum_agreement_card]
  calc
    family.G.card * (h + 1) = ∑ _gamma ∈ family.G, (h + 1) := by simp
    _ ≤ ∑ gamma ∈ family.G, ((selectedAgreements family gamma).card) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      rw [← hthreshold]
      exact family.threshold_le gamma hgamma

/-- The coordinate third moment is exactly the unordered common-coordinate weight sum. -/
theorem thirdMoment_eq_weightedTripleSum
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) :
    (∑ i, (incidenceMultiplicity family i).choose 3) =
      ∑ T ∈ family.G.powersetCard 3, tripleWeight family T := by
  exact sum_choose_incidence_eq_sum_commonCoordinates_card
    family.G (selectedAgreements family)

/-! ## Geometric inputs to the abstract weighted-triple bound -/

/-- Every relevant line has the low-core inequality in the counterexample range. -/
theorem jointCore_card_bound_of_card_gt_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 ≤
      h + 4 * (k - 1) := by
  have hh : 8 ≤ h := eight_le_half_of_rateSixteenth rfl hk hrate
  by_contra hnot
  have hlarge : h + 4 * (k - 1) <
      2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 := by
    omega
  exact largeCore_contradiction_of_card_gt_two_mul family (by omega) hk hn
    (hthreshold.ge) hline hcard hlarge

/-- In the counterexample range, the large-core collapse and fresh-fibre packing force every
canonical polynomial line to contain at most four selected scalar points. -/
theorem pointsOn_card_le_four_of_card_gt_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) (hcard : 2 * h < family.G.card)
    (line : LineParameter F) :
    (pointsOn family line).card ≤ 4 := by
  by_cases hlineSmall : (pointsOn family line).card ≤ 1
  · omega
  have hlineTwo : 1 < (pointsOn family line).card := by omega
  obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ :=
    Finset.one_lt_card.mp hlineTwo
  have hgammaG : gamma ∈ family.G := pointsOn_subset_G family line hgamma
  have hbetaG : beta ∈ family.G := pointsOn_subset_G family line hbeta
  have hsecant : secantParameter family gamma beta = line :=
    secantParameter_eq_of_mem_pointsOn family line hgamma hbeta hgb
  have hline : line ∈ lineParameters family := by
    rw [← hsecant]
    exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  have hh : 8 ≤ h := eight_le_half_of_rateSixteenth rfl hk hrate
  have hdegreeRate : 8 * (k - 1) + 8 ≤ h :=
    degree_pred_rate_bound rfl hk hrate
  have hcore : 2 * z + 3 ≤ h + 4 * (k - 1) :=
    jointCore_card_bound_of_card_gt_two_mul family hk hn hthreshold hrate hcard hline
  have hpacking := pointsOn_card_mul_max_add_core_le family hline
  rw [hthreshold, hn] at hpacking
  have hcount :
      (pointsOn family line).card * (h + 1 - z) + z ≤ 2 * h := by
    apply le_trans _ hpacking
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (pointsOn family line).card
        (le_max_right 1 (h + 1 - z))) z
  exact ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth.line_card_le_four
    hh hdegreeRate hcore hcount

/-- A noncollinear selected triple has at most the Reed--Solomon root-cap number of common
agreement coordinates. -/
theorem tripleWeight_le_degree_pred_of_not_collinear
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    (T : Finset F) (hT : T ∈ family.G.powersetCard 3)
    (hnoncol : ¬ Collinear (onFamilyLine family) T) :
    tripleWeight family T ≤ k - 1 := by
  have hTsub : T ⊆ family.G := (Finset.mem_powersetCard.mp hT).1
  have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  obtain ⟨gamma, beta, theta, hgb, hgt, hbt, rfl⟩ :=
    Finset.card_eq_three.mp hTcard
  have hgammaG : gamma ∈ family.G := hTsub (by simp)
  have hbetaG : beta ∈ family.G := hTsub (by simp)
  have hthetaG : theta ∈ family.G := hTsub (by simp)
  have hslope :
      slopePolynomial gamma beta (family.q gamma) (family.q beta) ≠
        slopePolynomial gamma theta (family.q gamma) (family.q theta) := by
    intro hslopeEq
    apply hnoncol
    refine ⟨secantParameter family gamma beta, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact first_point_mem_pointsOn_secant family hgammaG
    · exact second_point_mem_pointsOn_secant family hbetaG hgb
    · rw [onFamilyLine, mem_pointsOn_iff]
      refine ⟨hthetaG, ?_⟩
      simpa only [secantParameter] using
        (third_point_on_secant_line_of_slope_eq hgt hslopeEq.symm)
  have hcap := triple_fullAgreement_card_le_pred_of_slope_ne
    dom (u 0) (u 1) hk hgb hgt
    (family.degree_lt gamma hgammaG)
    (family.degree_lt beta hbetaG)
    (family.degree_lt theta hthetaG) hslope
  simpa only [tripleWeight, selectedAgreements, commonCoordinates_three] using hcap

/-- A collinear selected triple has weight at most `d+c`, where `d=k-1` and the integral
excess `c=(5h-20)/8` is the exact floor of the rational coefficient used by `upperSix`. -/
theorem tripleWeight_le_degree_pred_add_excess_of_collinear
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) (hcard : 2 * h < family.G.card)
    (T : Finset F) (hT : T ∈ collinearTriples family.G (onFamilyLine family)) :
    tripleWeight family T ≤ (k - 1) + (5 * h - 20) / 8 := by
  obtain ⟨hTsub, hTcard, ⟨line, hlineAll⟩⟩ :=
    (mem_collinearTriples_iff family.G (onFamilyLine family) T).mp hT
  obtain ⟨gamma, beta, theta, hgb, hgt, hbt, rfl⟩ :=
    Finset.card_eq_three.mp hTcard
  have hgammaG : gamma ∈ family.G := hTsub (by simp)
  have hbetaG : beta ∈ family.G := hTsub (by simp)
  have hthetaG : theta ∈ family.G := hTsub (by simp)
  have hgammaOn : gamma ∈ pointsOn family line := hlineAll gamma (by simp)
  have hbetaOn : beta ∈ pointsOn family line := hlineAll beta (by simp)
  have hthetaOn : theta ∈ pointsOn family line := hlineAll theta (by simp)
  have hline : line ∈ lineParameters family := by
    have hsecant := secantParameter_eq_of_mem_pointsOn
      family line hgammaOn hbetaOn hgb
    rw [← hsecant]
    exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  have hcore : 2 * D.card + 3 ≤ h + 4 * (k - 1) :=
    jointCore_card_bound_of_card_gt_two_mul family hk hn hthreshold hrate hcard hline
  have hdegreeRate : 8 * (k - 1) + 8 ≤ h :=
    degree_pred_rate_bound rfl hk hrate
  have hDbound : D.card ≤ (k - 1) + (5 * h - 20) / 8 := by
    omega
  have hgammaEq := (mem_pointsOn_iff family line gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line beta).mp hbetaOn |>.2
  have hthetaEq := (mem_pointsOn_iff family line theta).mp hthetaOn |>.2
  have hpairCore :
      selectedAgreements family gamma ∩ selectedAgreements family beta = D := by
    simp only [selectedAgreements, D, hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line.1 line.2 hgb
  have hcoreSubset : D ⊆ selectedAgreements family theta := by
    simp only [selectedAgreements, hthetaEq, D]
    exact jointCore_subset_fullAgreement
      dom (u 0) (u 1) line.1 line.2 theta
  simpa only [tripleWeight, commonCoordinates_three, hpairCore,
    Finset.inter_eq_left.mpr hcoreSubset] using hDbound

/-! ## Third-moment assembly -/

/-- The instantiated unordered weighted-triple upper bound. -/
theorem weightedTripleSum_nat_upper
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) (hcard : 2 * h < family.G.card) :
    6 * (∑ T ∈ family.G.powersetCard 3, tripleWeight family T) ≤
      (k - 1) * family.G.card * (family.G.card - 1) * (family.G.card - 2) +
        2 * ((5 * h - 20) / 8) * family.G.card * (family.G.card - 1) := by
  apply weightedTripleSum_upper family.G (onFamilyLine family)
    (secantParameter family) (tripleWeight family) (k - 1) ((5 * h - 20) / 8)
  · intro gamma hgamma beta hbeta hgb
    exact ⟨first_point_mem_pointsOn_secant family hgamma,
      second_point_mem_pointsOn_secant family hbeta hgb⟩
  · intro line gamma beta hgb hgamma hbeta
    exact (secantParameter_eq_of_mem_pointsOn
      family line hgamma hbeta hgb).symm
  · intro line
    rw [linePoints_eq_pointsOn]
    exact pointsOn_card_le_four_of_card_gt_two_mul
      family hk hn hthreshold hrate hcard line
  · intro T hT hnoncol
    exact tripleWeight_le_degree_pred_of_not_collinear family hk T hT hnoncol
  · intro T hT
    exact tripleWeight_le_degree_pred_add_excess_of_collinear
      family hk hn hthreshold hrate hcard T hT

/-- Rational form of the instantiated upper bound, normalized to `upperSix`. -/
theorem weightedTripleSum_rat_upper
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) (hcard : 2 * h < family.G.card) :
    6 * (∑ T ∈ family.G.powersetCard 3, (tripleWeight family T : ℚ)) ≤
      upperSix h family.G.card := by
  have hh : 8 ≤ h := eight_le_half_of_rateSixteenth rfl hk hrate
  have hNtwo : 2 ≤ family.G.card := by omega
  have hNone : 1 ≤ family.G.card := by omega
  have hnat := weightedTripleSum_nat_upper
    family hk hn hthreshold hrate hcard
  have hcast :
      ((6 * (∑ T ∈ family.G.powersetCard 3, tripleWeight family T) : ℕ) : ℚ) ≤
        (((k - 1) * family.G.card * (family.G.card - 1) *
            (family.G.card - 2) +
          2 * ((5 * h - 20) / 8) * family.G.card *
            (family.G.card - 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  push_cast [Nat.cast_sub hNone, Nat.cast_sub hNtwo] at hcast
  have hdegreeRate : 8 * (k - 1) + 8 ≤ h :=
    degree_pred_rate_bound rfl hk hrate
  have hdQ : ((k - 1 : ℕ) : ℚ) ≤ (h : ℚ) / 8 - 1 :=
    degree_coefficient_rational_le hdegreeRate
  have htwenty : 20 ≤ 5 * h := by omega
  have hcNat : 8 * ((5 * h - 20) / 8) ≤ 5 * h - 20 := by
    have hdiv := Nat.div_mul_le_self (5 * h - 20) 8
    omega
  have hcRaw :
      (8 : ℚ) * (((5 * h - 20) / 8 : ℕ) : ℚ) ≤
        5 * (h : ℚ) - 20 := by
    exact_mod_cast hcNat
  have hcQ : (((5 * h - 20) / 8 : ℕ) : ℚ) ≤
      5 * (h : ℚ) / 8 - 5 / 2 := by
    linarith
  have hN1Q : (1 : ℚ) ≤ family.G.card := by exact_mod_cast hNone
  have hN2Q : (2 : ℚ) ≤ family.G.card := by exact_mod_cast hNtwo
  have hfirst :
      ((k - 1 : ℕ) : ℚ) * family.G.card * (family.G.card - 1) *
          (family.G.card - 2) ≤
        ((h : ℚ) / 8 - 1) * family.G.card * (family.G.card - 1) *
          (family.G.card - 2) := by
    gcongr <;> linarith
  have hsecond :
      2 * (((5 * h - 20) / 8 : ℕ) : ℚ) * family.G.card *
          (family.G.card - 1) ≤
        2 * (5 * (h : ℚ) / 8 - 5 / 2) * family.G.card *
          (family.G.card - 1) := by
    gcongr
    linarith
  exact hcast.trans (by
    simpa only [upperSix] using add_le_add hfirst hsecond)

/-! ## Final half-predecessor bound -/

/-- **Rate-`1/16` half-predecessor incidence theorem.** Any selected bad-scalar rich-point
family at the exact half-predecessor threshold has at most `2h` points. -/
theorem badScalarRichPointFamily_card_le_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 16 * k ≤ 2 * h) :
    family.G.card ≤ 2 * h := by
  by_contra hnot
  have hcard : 2 * h < family.G.card := by omega
  have hh : 8 ≤ h := eight_le_half_of_rateSixteenth rfl hk hrate
  have hN : 2 * h + 1 ≤ family.G.card := by omega
  have hsum : family.G.card * (h + 1) ≤
      ∑ i, incidenceMultiplicity family i :=
    total_incidence_lower family hthreshold
  have hlower : lowerSix h family.G.card ≤
      6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) := by
    simpa only [lowerSix] using
      (thirdMoment_jensen_lower_rat (incidenceMultiplicity family)
        h family.G.card (by omega) hn hN hsum)
  have hmomentNat := thirdMoment_eq_weightedTripleSum family
  have hmoment :
      (∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ)) =
        ∑ T ∈ family.G.powersetCard 3, (tripleWeight family T : ℚ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℚ)) hmomentNat
    push_cast at hcast
    exact hcast
  have hupper :
      6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) ≤
        upperSix h family.G.card := by
    rw [hmoment]
    exact weightedTripleSum_rat_upper
      family hk hn hthreshold hrate hcard
  have hle := card_le_two_mul_of_thirdMoment_bounds h family.G.card
    (∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ)) hh hlower hupper
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
#print axioms total_incidence_lower
#print axioms thirdMoment_eq_weightedTripleSum
#print axioms pointsOn_card_le_four_of_card_gt_two_mul
#print axioms tripleWeight_le_degree_pred_of_not_collinear
#print axioms tripleWeight_le_degree_pred_add_excess_of_collinear
#print axioms weightedTripleSum_nat_upper
#print axioms weightedTripleSum_rat_upper
#print axioms badScalarRichPointFamily_card_le_two_mul
