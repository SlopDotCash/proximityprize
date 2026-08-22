/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorIncidenceAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThirdMomentJensenGeneral
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThirdMomentUpperLineCap

/-!
# The unconditional rate-`1/16` good point at `delta = 17/32`

For `32m` evaluation coordinates and agreement threshold `15m`, this file
fully wires the rich-point incidence argument.  A relevant line has at most
`17m+1` points.  A high core would put the whole family on two such lines, so
a counterexample to the target `64m` bad-scalar bound has only low cores.
Low-core packing then gives the twelve-point line cap.  The arbitrary-line-cap
third-moment theorem contributes the exact factor ten, and generalized Jensen
gives the matching lower bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal BigOperators Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral
open ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap

namespace ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## Numeric gap for every counterexample size -/

/-- The quadratic factor of `lower-upper` at `delta=17/32`. -/
def gapQuadraticSeventeenThirtyTwo (h N : ℕ) : ℚ :=
  (1 + 1327 * (h : ℚ) / 16384) * (N : ℚ)^2 +
    (7 - 4163 * (h : ℚ) / 512) * (N : ℚ) +
    141 * (h : ℚ) / 16 - 8

/-- Exact factorization of the all-`N` numeric gap. -/
theorem lower_sub_upper_seventeenThirtyTwo_eq (h N : ℕ) :
    lowerSixSeventeenThirtyTwo h N - upperSixSeventeenThirtyTwo h N =
      (N : ℚ) * gapQuadraticSeventeenThirtyTwo h N := by
  simp only [lowerSixSeventeenThirtyTwo, upperSixSeventeenThirtyTwo,
    gapQuadraticSeventeenThirtyTwo]
  ring

/-- The quadratic gap is increasing from `N=4h+1`. -/
theorem gapQuadraticSeventeenThirtyTwo_mono
    (h N : ℕ) (hN : 4 * h + 1 ≤ N) :
    gapQuadraticSeventeenThirtyTwo h (4 * h + 1) ≤
      gapQuadraticSeventeenThirtyTwo h N := by
  let A : ℚ := 1 + 1327 * (h : ℚ) / 16384
  let B : ℚ := 7 - 4163 * (h : ℚ) / 512
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hNq : (4 * (h : ℚ) + 1) ≤ (N : ℚ) := by
    exact_mod_cast hN
  have hsum : 2 * (4 * (h : ℚ) + 1) ≤
      (N : ℚ) + (4 * (h : ℚ) + 1) := by linarith
  have hbase : 0 < A * (2 * (4 * (h : ℚ) + 1)) + B := by
    have hid : A * (2 * (4 * (h : ℚ) + 1)) + B =
        1327 * (h : ℚ)^2 / 2048 +
          255 * (h : ℚ) / 8192 + 9 := by
      simp only [A, B]
      ring
    rw [hid]
    positivity
  have hbracket : 0 ≤
      A * ((N : ℚ) + (4 * (h : ℚ) + 1)) + B := by
    have hmul := mul_le_mul_of_nonneg_left hsum hA.le
    linarith
  have hfactor :
      gapQuadraticSeventeenThirtyTwo h N -
          gapQuadraticSeventeenThirtyTwo h (4 * h + 1) =
        ((N : ℚ) - (4 * (h : ℚ) + 1)) *
          (A * ((N : ℚ) + (4 * (h : ℚ) + 1)) + B) := by
    simp only [gapQuadraticSeventeenThirtyTwo, A, B]
    push_cast
    ring
  apply sub_nonneg.mp
  rw [hfactor]
  exact mul_nonneg (sub_nonneg.mpr hNq) hbracket

/-- The strict `17/32` third-moment gap holds for every `N>=4h+1`, not only
at the endpoint. -/
theorem upperSixSeventeenThirtyTwo_lt_lower_of_ge
    (h N : ℕ) (hh : 16 ≤ h) (hN : 4 * h + 1 ≤ N) :
    upperSixSeventeenThirtyTwo h N < lowerSixSeventeenThirtyTwo h N := by
  have hend := upperSixSeventeenThirtyTwo_lt_lower h hh
  have hidEnd := lower_sub_upper_seventeenThirtyTwo_eq h (4 * h + 1)
  have hN0q : (0 : ℚ) < (4 * h + 1 : ℕ) := by positivity
  have hgapEnd : 0 < gapQuadraticSeventeenThirtyTwo h (4 * h + 1) := by
    nlinarith
  have hmono := gapQuadraticSeventeenThirtyTwo_mono h N hN
  have hgap : 0 < gapQuadraticSeventeenThirtyTwo h N :=
    hgapEnd.trans_le hmono
  have hid := lower_sub_upper_seventeenThirtyTwo_eq h N
  have hNq : (0 : ℚ) < (N : ℚ) := by
    exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hNq hgap]

/-! ## Line caps and low cores -/

/-- Every relevant line at threshold `15m` has at most `17m+1` points. -/
theorem relevantLine_card_le_seventeen_mul_add_one
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (pointsOn family line).card ≤ 17 * m + 1 := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  have hpacking := pointsOn_card_mul_max_add_core_le family hline
  rw [hthreshold, hn] at hpacking
  have hz : z ≤ 32 * m := by
    have := Finset.card_le_univ
      (jointCore dom (u 0) (u 1) line.1 line.2)
    rw [hn] at this
    exact this
  have hL := two_le_pointsOn_card_of_mem_lineParameters family hline
  have hcap := line_card_le_complement_threshold_succ
    (n := 32 * m) (t := 15 * m) (z := z)
    (L := (pointsOn family line).card)
    (by omega) hz (by omega) hpacking
  omega

/-- In a counterexample to the `64m` bound, every relevant line has the
surviving low-core inequality `2z <= 19m+4d`. -/
theorem relevantLine_low_core
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) (hcard : 64 * m < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    2 * (jointCore dom (u 0) (u 1) line.1 line.2).card ≤
      19 * m + 4 * (k - 1) := by
  have hm : 1 ≤ m := by omega
  have htd : k - 1 ≤ 15 * m := by omega
  have hlarge : ∀ gamma ∈ family.G,
      15 * m ≤ (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card := by
    intro gamma hgamma
    rw [← hthreshold]
    exact family.threshold_le gamma hgamma
  have hlineCap : ∀ ell ∈ lineParameters family,
      (pointsOn family ell).card ≤ 17 * m + 1 := by
    intro ell hell
    exact relevantLine_card_le_seventeen_mul_add_one
      family hn hthreshold hell
  have hcardTwo : 2 * (17 * m + 1) < family.G.card := by omega
  have hlow := low_core_of_card_gt_two_mul_lineCap
    family hk htd hlarge hlineCap hcardTwo hline
  rw [hn] at hlow
  omega

/-- Every polynomial line, relevant or not, has at most twelve selected
points in the counterexample range. -/
theorem allLines_card_le_twelve
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) (hcard : 64 * m < family.G.card)
    (line : LineParameter F) :
    (pointsOn family line).card ≤ 12 := by
  by_cases hsmall : (pointsOn family line).card ≤ 1
  · omega
  obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ :=
    Finset.one_lt_card.mp (show 1 < (pointsOn family line).card by omega)
  have hgammaG := pointsOn_subset_G family line hgamma
  have hbetaG := pointsOn_subset_G family line hbeta
  have hsecant := secantParameter_eq_of_mem_pointsOn
    family line hgamma hbeta hgb
  have hline : line ∈ lineParameters family := by
    rw [← hsecant]
    exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  have hm : 1 ≤ m := by omega
  have hdegreeRate : 8 * (k - 1) + 8 ≤ 16 * m := by omega
  have hcore : 2 * z ≤ 19 * m + 4 * (k - 1) :=
    relevantLine_low_core family hk hn hthreshold hrate hcard hline
  have hz : z < 15 * m := by omega
  have hpacking := pointsOn_card_mul_max_add_core_le family hline
  rw [hthreshold, hn] at hpacking
  have hcount :
      (pointsOn family line).card * (15 * m - z) + z ≤ 32 * m := by
    apply le_trans _ hpacking
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (pointsOn family line).card
        (le_max_right 1 (15 * m - z))) z
  exact line_card_le_twelve_seventeenThirtyTwo
    hm hdegreeRate hcore hcount

/-! ## Triple weights and moment upper bound -/

/-- Integral upper bound for the excess of a collinear triple over the root
cap. -/
def seventeenThirtyTwoExcess (m d : ℕ) : ℕ :=
  (19 * m + 2 * d) / 2

theorem core_card_le_degree_add_excess
    {m d z : ℕ} (hcore : 2 * z ≤ 19 * m + 4 * d) :
    z ≤ d + seventeenThirtyTwoExcess m d := by
  by_cases hzd : z ≤ d
  · exact hzd.trans (Nat.le_add_right d _)
  · have hsub : 2 * (z - d) ≤ 19 * m + 2 * d := by omega
    have hdiv : z - d ≤ (19 * m + 2 * d) / 2 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      simpa only [Nat.mul_comm] using hsub
    have hsplit : z - d + d = z := Nat.sub_add_cancel (by omega)
    dsimp only [seventeenThirtyTwoExcess]
    omega

/-- Rational coefficient bound matching `upperSixSeventeenThirtyTwo`. -/
theorem seventeenThirtyTwoExcess_cast_le
    {m d : ℕ} (hrate : 8 * d + 8 ≤ 16 * m) :
    (seventeenThirtyTwoExcess m d : ℚ) ≤
      23 * (m : ℚ) / 2 - 1 := by
  have hm : 1 ≤ m := by omega
  have hmul := Nat.mul_div_le (19 * m + 2 * d) 2
  have hmulQ :
      (2 : ℚ) * (seventeenThirtyTwoExcess m d : ℚ) ≤
        19 * (m : ℚ) + 2 * (d : ℚ) := by
    have hnat :
        2 * seventeenThirtyTwoExcess m d ≤ 19 * m + 2 * d := by
      simpa only [seventeenThirtyTwoExcess] using hmul
    exact_mod_cast hnat
  have hdQ : (d : ℚ) ≤ 2 * (m : ℚ) - 1 := by
    have : (8 : ℚ) * (d : ℚ) + 8 ≤ 16 * (m : ℚ) := by
      exact_mod_cast hrate
    linarith
  linarith

/-- A collinear selected triple has weight at most `d` plus the integral
`17/32` excess coefficient. -/
theorem tripleWeight_le_degree_add_excess_of_collinear
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) (hcard : 64 * m < family.G.card)
    (T : Finset F)
    (hT : T ∈ collinearTriples family.G (onFamilyLine family)) :
    tripleWeight family T ≤
      (k - 1) + seventeenThirtyTwoExcess m (k - 1) := by
  obtain ⟨hTsub, hTcard, ⟨line, hlineAll⟩⟩ :=
    (mem_collinearTriples_iff family.G (onFamilyLine family) T).mp hT
  obtain ⟨gamma, beta, theta, hgb, hgt, hbt, rfl⟩ :=
    Finset.card_eq_three.mp hTcard
  have hgammaG : gamma ∈ family.G := hTsub (by simp)
  have hbetaG : beta ∈ family.G := hTsub (by simp)
  have hgammaOn : gamma ∈ pointsOn family line :=
    hlineAll gamma (by simp)
  have hbetaOn : beta ∈ pointsOn family line :=
    hlineAll beta (by simp)
  have hthetaOn : theta ∈ pointsOn family line :=
    hlineAll theta (by simp)
  have hline : line ∈ lineParameters family := by
    have hsecant := secantParameter_eq_of_mem_pointsOn
      family line hgammaOn hbetaOn hgb
    rw [← hsecant]
    exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  have hcore : 2 * D.card ≤ 19 * m + 4 * (k - 1) :=
    relevantLine_low_core family hk hn hthreshold hrate hcard hline
  have hDbound : D.card ≤
      (k - 1) + seventeenThirtyTwoExcess m (k - 1) :=
    core_card_le_degree_add_excess hcore
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

/-- Instantiated natural weighted-triple upper bound with the twelve-point
line cap. -/
theorem weightedTripleSum_nat_upper_seventeenThirtyTwo
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) (hcard : 64 * m < family.G.card) :
    6 * (∑ T ∈ family.G.powersetCard 3, tripleWeight family T) ≤
      (k - 1) * family.G.card * (family.G.card - 1) *
          (family.G.card - 2) +
        10 * seventeenThirtyTwoExcess m (k - 1) *
          family.G.card * (family.G.card - 1) := by
  apply weightedTripleSum_upper_lineCap family.G (onFamilyLine family)
    (secantParameter family) (tripleWeight family)
    (k - 1) (seventeenThirtyTwoExcess m (k - 1)) 12
  · intro gamma hgamma beta hbeta hgb
    exact ⟨first_point_mem_pointsOn_secant family hgamma,
      second_point_mem_pointsOn_secant family hbeta hgb⟩
  · intro line gamma beta hgb hgamma hbeta
    exact (secantParameter_eq_of_mem_pointsOn
      family line hgamma hbeta hgb).symm
  · intro line
    rw [linePoints_eq_pointsOn]
    exact allLines_card_le_twelve
      family hk hn hthreshold hrate hcard line
  · intro T hT hnoncol
    exact tripleWeight_le_degree_pred_of_not_collinear
      family hk T hT hnoncol
  · intro T hT
    exact tripleWeight_le_degree_add_excess_of_collinear
      family hk hn hthreshold hrate hcard T hT

/-- Rationalized upper bound in the exact numeric-core form. -/
theorem thirdMoment_upper_rat_seventeenThirtyTwo
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) (hcard : 64 * m < family.G.card) :
    6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) ≤
      upperSixSeventeenThirtyTwo (16 * m) family.G.card := by
  have hnat := weightedTripleSum_nat_upper_seventeenThirtyTwo
    family hk hn hthreshold hrate hcard
  rw [← thirdMoment_eq_weightedTripleSum family] at hnat
  have hNtwo : 2 ≤ family.G.card := by omega
  have hNone : 1 ≤ family.G.card := by omega
  have hcast :
      6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) ≤
        ((k - 1 : ℕ) : ℚ) * (family.G.card : ℚ) *
            ((family.G.card : ℚ) - 1) * ((family.G.card : ℚ) - 2) +
          10 * (seventeenThirtyTwoExcess m (k - 1) : ℚ) *
            (family.G.card : ℚ) * ((family.G.card : ℚ) - 1) := by
    exact_mod_cast hnat
  have hdegreeRate : 8 * (k - 1) + 8 ≤ 16 * m := by omega
  have hdQ : ((k - 1 : ℕ) : ℚ) ≤ 2 * (m : ℚ) - 1 := by
    have : (8 : ℚ) * ((k - 1 : ℕ) : ℚ) + 8 ≤
        16 * (m : ℚ) := by exact_mod_cast hdegreeRate
    linarith
  have hcQ := seventeenThirtyTwoExcess_cast_le hdegreeRate
  have hN1Q : (1 : ℚ) ≤ family.G.card := by exact_mod_cast hNone
  have hN2Q : (2 : ℚ) ≤ family.G.card := by exact_mod_cast hNtwo
  have hfirst :
      ((k - 1 : ℕ) : ℚ) * family.G.card * (family.G.card - 1) *
          (family.G.card - 2) ≤
        (2 * (m : ℚ) - 1) * family.G.card * (family.G.card - 1) *
          (family.G.card - 2) := by
    gcongr <;> linarith
  have hsecond :
      10 * (seventeenThirtyTwoExcess m (k - 1) : ℚ) *
          family.G.card * (family.G.card - 1) ≤
        10 * (23 * (m : ℚ) / 2 - 1) *
          family.G.card * (family.G.card - 1) := by
    gcongr
    linarith
  calc
    6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) ≤ _ := hcast
    _ ≤ (2 * (m : ℚ) - 1) * family.G.card *
          (family.G.card - 1) * (family.G.card - 2) +
        10 * (23 * (m : ℚ) / 2 - 1) * family.G.card *
          (family.G.card - 1) := add_le_add hfirst hsecond
    _ = upperSixSeventeenThirtyTwo (16 * m) family.G.card := by
      simp only [upperSixSeventeenThirtyTwo]
      push_cast
      ring

/-! ## Jensen lower bound and family theorem -/

/-- Threshold richness gives the total incidence `15m*N`. -/
theorem total_incidence_lower_seventeenThirtyTwo
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m) :
    family.G.card * (15 * m) ≤
      ∑ i, incidenceMultiplicity family i := by
  rw [sum_incidenceMultiplicity_eq_sum_agreement_card]
  calc
    family.G.card * (15 * m) =
        ∑ _gamma ∈ family.G, (15 * m) := by simp
    _ ≤ ∑ gamma ∈ family.G,
        (selectedAgreements family gamma).card := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      rw [← hthreshold]
      exact family.threshold_le gamma hgamma

/-- Generalized Jensen in the exact `lowerSixSeventeenThirtyTwo` form. -/
theorem lowerSix_le_thirdMoment_seventeenThirtyTwo
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hm : 1 ≤ m) (hcard : 64 * m < family.G.card) :
    lowerSixSeventeenThirtyTwo (16 * m) family.G.card ≤
      6 * ∑ i, ((incidenceMultiplicity family i).choose 3 : ℚ) := by
  have hsum := total_incidence_lower_seventeenThirtyTwo family hthreshold
  have htwo : 2 * (32 * m) ≤ family.G.card * (15 * m) := by
    have hN : 64 * m + 1 ≤ family.G.card := by omega
    nlinarith
  have hjensen := thirdMoment_jensen_lower_rat_general
    (incidenceMultiplicity family) (32 * m) family.G.card (15 * m)
    (by positivity) hn htwo hsum
  dsimp only at hjensen
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have ha :
      (family.G.card : ℚ) * (15 * m : ℕ) / (32 * m : ℕ) =
        15 * (family.G.card : ℚ) / 32 := by
    push_cast
    field_simp [hmQ]
  rw [ha] at hjensen
  have hscale : ((32 * m : ℕ) : ℚ) = 2 * ((16 * m : ℕ) : ℚ) := by
    push_cast
    ring
  simp only [lowerSixSeventeenThirtyTwo]
  rw [← hscale]
  exact hjensen

/-- **Complete `17/32` family theorem.** At rate at most `1/16`, at most
twice the code length many scalars can be bad. -/
theorem badScalarRichPointFamily_card_le_sixtyFour_mul
    {dom : ι ↪ F} {k m : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) :
    family.G.card ≤ 64 * m := by
  by_contra hnot
  have hcard : 64 * m < family.G.card := by omega
  have hm : 1 ≤ m := by omega
  have hlower := lowerSix_le_thirdMoment_seventeenThirtyTwo
    family hn hthreshold hm hcard
  have hupper := thirdMoment_upper_rat_seventeenThirtyTwo
    family hk hn hthreshold hrate hcard
  have hN : 4 * (16 * m) + 1 ≤ family.G.card := by omega
  have hgap := upperSixSeventeenThirtyTwo_lt_lower_of_ge
    (16 * m) family.G.card (by omega) hN
  linarith

/-- Canonical selected-family form. -/
theorem canonicalRichPointFamily_card_le_sixtyFour_mul
    (dom : ι ↪ F) {k m : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) :
    (canonicalBadScalarRichPointFamily dom delta u hk).G.card ≤ 64 * m :=
  badScalarRichPointFamily_card_le_sixtyFour_mul
    (canonicalBadScalarRichPointFamily dom delta u hk)
    hk hn hthreshold hrate

/-- Literal event-filter form at an arbitrary radius with ceiling `15m`. -/
theorem badScalar_filter_card_le_sixtyFour_mul
    (dom : ι ↪ F) {k m : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 32 * m)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = 15 * m)
    (hrate : 16 * k ≤ 32 * m) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma).card ≤ 64 * m := by
  simpa only [canonicalBadScalarRichPointFamily, badScalars] using
    canonicalRichPointFamily_card_le_sixtyFour_mul
      dom delta u hk hn hthreshold hrate

/-! ## Literal radius `17/32` -/

/-- The agreement ceiling at radius `17/32` in `32m` coordinates is exactly
`15m`. -/
theorem seventeenThirtyTwo_ceiling_agreement_eq (m : ℕ) :
    ⌈(1 - (17 / 32 : ℝ≥0)) * ((32 * m : ℕ) : ℝ≥0)⌉₊ = 15 * m := by
  have hsub : (1 - (17 / 32 : ℝ≥0)) = (15 / 32 : ℝ≥0) := by
    ext
    rw [NNReal.coe_sub (by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 32)).2
      norm_num : (17 / 32 : ℝ≥0) ≤ 1)]
    norm_num
  have hcalc :
      (1 - (17 / 32 : ℝ≥0)) * ((32 * m : ℕ) : ℝ≥0) =
        ((15 * m : ℕ) : ℝ≥0) := by
    rw [hsub]
    ext
    simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat,
      Nat.cast_mul, Nat.cast_ofNat]
    norm_num
    ring
  rw [hcalc, Nat.ceil_natCast]

/-- **Literal uniform `17/32` bad-count theorem.** For a length `n=32m`
rate-`1/16` RS code, the bad-scalar filter has cardinality at most `2n`. -/
theorem seventeenThirtyTwo_badScalar_filter_card_le_two_mul_length
    {n m k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 32 * m) (hk : 1 ≤ k) (hrate : 16 * k ≤ n)
    (u : WordStack F (Fin 2) (Fin n)) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent ((ReedSolomon.code dom k : Set (Fin n → F)))
        (17 / 32 : ℝ≥0) (u 0) (u 1) gamma).card ≤ 2 * n := by
  have hcardFin : Fintype.card (Fin n) = 32 * m := by simp [hn]
  have hthreshold :
      ⌈(1 - (17 / 32 : ℝ≥0)) *
          (Fintype.card (Fin n) : ℝ≥0)⌉₊ = 15 * m := by
    rw [Fintype.card_fin, hn]
    exact seventeenThirtyTwo_ceiling_agreement_eq m
  have hbound := badScalar_filter_card_le_sixtyFour_mul
    dom (17 / 32 : ℝ≥0) u hk hcardFin hthreshold (by omega)
  omega

end ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring.badScalarRichPointFamily_card_le_sixtyFour_mul
#print axioms
  ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring.seventeenThirtyTwo_badScalar_filter_card_le_two_mul_length
