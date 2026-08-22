/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorIncidenceAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthCombinatorics
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthNumeric
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R387RateEighthPrunedMoment

/-!
# Literal rate-`1/8` half-predecessor bad-scalar bound

This file connects the canonical Reed--Solomon secant geometry to the
Johnson-pruning and pruned third-moment engines.  Unlike the first abstract
rate-`1/8` consumer, the result is stated for every even length `n=2h`; no
divisibility assumption on `h` is used.  The two Johnson strata use
`h / 4` and `h / 16`, with the possible remainders retained in the arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal BigOperators Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthArithmeticBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthCombinatorics
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## Johnson arithmetic without a divisibility hypothesis -/

/-- Cores forced by five-point lines form a family of size at most fifteen,
including all four possible residues of `h` modulo four. -/
theorem exceptional_core_family_card_le_fifteen_generic
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (h k : ℕ) (hh : 1699 ≤ h) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (E : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ E, 3 * (h / 4) + 2 ≤ (core line).card)
    (hinter : ∀ line ∈ E, ∀ line' ∈ E, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1) :
    E.card ≤ 15 := by
  let q := h / 4
  have hq : 1 ≤ q := by
    dsimp only [q]
    omega
  have hkq : k ≤ q := by
    dsimp only [q]
    omega
  have hdZ : k - 1 ≤ 3 * q + 2 := by omega
  have hJ :=
    ArkLib.ProximityGap.Frontier.R387RateEighthPruning.johnson_core_packing
      E core (3 * q + 2) (k - 1) hdZ
      (by simpa only [q] using hsize) hinter
  rw [hU] at hJ
  by_contra hnot
  have hE : 16 ≤ E.card := by omega
  have hhq : 4 * q ≤ h := by
    dsimp only [q]
    omega
  have hhq' : h ≤ 4 * q + 3 := by
    dsimp only [q]
    omega
  have hkpred : k - 1 ≤ q - 1 := by omega
  have hq1 : 1 ≤ q := by omega
  have hkpredCast : ((k - 1 : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    have hkqR : (k : ℝ) ≤ q := by exact_mod_cast hkq
    linarith
  have hhqR : (4 : ℝ) * q ≤ h := by exact_mod_cast hhq
  have hhqR' : (h : ℝ) ≤ 4 * q + 3 := by exact_mod_cast hhq'
  have hER : (16 : ℝ) ≤ E.card := by exact_mod_cast hE
  have hprod : (h : ℝ) * ((k - 1 : ℕ) : ℝ) ≤
      (4 * (q : ℝ) + 3) * ((q : ℝ) - 1) := by
    exact mul_le_mul hhqR' hkpredCast (by positivity) (by positivity)
  have hpolypos : (0 : ℝ) <
      (3 * (q : ℝ) + 2) ^ 2 -
        2 * (4 * (q : ℝ) + 3) * ((q : ℝ) - 1) := by
    nlinarith [sq_nonneg (q : ℝ)]
  have hcoef : (0 : ℝ) <
      (3 * (q : ℝ) + 2) ^ 2 - 2 * (h : ℝ) * (k - 1 : ℕ) := by
    nlinarith
  have hlow := mul_le_mul_of_nonneg_right hER hcoef.le
  have hprodZ : (h : ℝ) * (3 * (q : ℝ) + 2) ≤
      (4 * (q : ℝ) + 3) * (3 * (q : ℝ) + 2) := by
    exact mul_le_mul_of_nonneg_right hhqR' (by positivity)
  have hJ' :
      (E.card : ℝ) *
          ((3 * (q : ℝ) + 2) ^ 2 -
            2 * (h : ℝ) * ((k - 1 : ℕ) : ℝ)) ≤
        2 * (h : ℝ) *
          (3 * (q : ℝ) + 2 - ((k - 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
      using hJ
  nlinarith

/-- Ultra cores form a family of size at most three, including all sixteen
possible residues of `h` modulo sixteen. -/
theorem ultra_core_family_card_le_three_generic
    {U Line : Type*} [Fintype U] [DecidableEq U] [DecidableEq Line]
    (h k : ℕ) (hh : 1699 ≤ h) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (Q : Finset Line) (core : Line → Finset U)
    (hsize : ∀ line ∈ Q, 15 * (h / 16) + 1 ≤ (core line).card)
    (hinter : ∀ line ∈ Q, ∀ line' ∈ Q, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1) :
    Q.card ≤ 3 := by
  let q := h / 16
  have hq : 26 ≤ q := by
    dsimp only [q]
    omega
  have hhq : 16 * q ≤ h := by
    dsimp only [q]
    omega
  have hhq' : h ≤ 16 * q + 15 := by
    dsimp only [q]
    omega
  have hkq : k ≤ 4 * q + 3 := by omega
  have hdZ : k - 1 ≤ 15 * q + 1 := by omega
  have hJ :=
    ArkLib.ProximityGap.Frontier.R387RateEighthPruning.johnson_core_packing
      Q core (15 * q + 1) (k - 1) hdZ
      (by simpa only [q] using hsize) hinter
  rw [hU] at hJ
  by_contra hnot
  have hQ : 4 ≤ Q.card := by omega
  have hqR : (26 : ℝ) ≤ q := by exact_mod_cast hq
  have hhqR : (16 : ℝ) * q ≤ h := by exact_mod_cast hhq
  have hhqR' : (h : ℝ) ≤ 16 * q + 15 := by exact_mod_cast hhq'
  have hkqR : ((k - 1 : ℕ) : ℝ) ≤ 4 * q + 2 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    have hkqR' : (k : ℝ) ≤ 4 * q + 3 := by exact_mod_cast hkq
    linarith
  have hQR : (4 : ℝ) ≤ Q.card := by exact_mod_cast hQ
  have hprod : (h : ℝ) * ((k - 1 : ℕ) : ℝ) ≤
      (16 * (q : ℝ) + 15) * (4 * (q : ℝ) + 2) := by
    exact mul_le_mul hhqR' hkqR (by positivity) (by positivity)
  have hpolypos : (0 : ℝ) <
      (15 * (q : ℝ) + 1) ^ 2 -
        2 * (16 * (q : ℝ) + 15) * (4 * (q : ℝ) + 2) := by
    nlinarith [sq_nonneg ((q : ℝ) - 26)]
  have hcoef : (0 : ℝ) <
      (15 * (q : ℝ) + 1) ^ 2 - 2 * (h : ℝ) * (k - 1 : ℕ) := by
    nlinarith
  have hlow := mul_le_mul_of_nonneg_right hQR hcoef.le
  have hprodZ : (h : ℝ) * (15 * (q : ℝ) + 1) ≤
      (16 * (q : ℝ) + 15) * (15 * (q : ℝ) + 1) := by
    exact mul_le_mul_of_nonneg_right hhqR' (by positivity)
  have hJ' :
      (Q.card : ℝ) *
          ((15 * (q : ℝ) + 1) ^ 2 -
            2 * (h : ℝ) * ((k - 1 : ℕ) : ℝ)) ≤
        2 * (h : ℝ) *
          (15 * (q : ℝ) + 1 - ((k - 1 : ℕ) : ℝ)) := by
    convert hJ using 1 <;> push_cast <;> ring
  nlinarith [sq_nonneg ((q : ℝ) - 26)]

/-! ## A generic pruned-moment consumer -/

/-- The pruned third-moment contradiction in arbitrary even length.  The
collinear input is expressed by the global core ceiling `h-4`; comparison
with the rational rate-`1/8` bulk bound is joint in the base and excess terms,
so no rounding loss occurs when `4 ∤ h`. -/
theorem card_le_two_mul_of_pruned_geometry
    {U Gamma Line : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq Gamma] [DecidableEq Line]
    (h k : ℕ) (hh : 1699 ≤ h) (hk : 1 ≤ k) (hrate : 4 * k ≤ h)
    (hU : Fintype.card U = 2 * h)
    (G R : Finset Gamma) (A : Gamma → Finset U)
    (onLine : Line → Gamma → Prop) (determinedLine : Gamma → Gamma → Line)
    (hRG : R ⊆ G) (hRcard : 7 * R.card ≤ 5 * h)
    (hsize : ∀ gamma ∈ G \ R, h + 1 ≤ (A gamma).card)
    (hpairOn : ∀ x ∈ G \ R, ∀ y ∈ G \ R, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints (G \ R) onLine ell).card ≤ 4)
    (hnoncol : ∀ T ∈ (G \ R).powersetCard 3, ¬ Collinear onLine T →
      (commonCoordinates A T).card ≤ k - 1)
    (hcol : ∀ T ∈ collinearTriples (G \ R) onLine,
      (commonCoordinates A T).card ≤ h - 4) :
    G.card ≤ 2 * h := by
  classical
  by_contra hnot
  have hG : 2 * h + 1 ≤ G.card := by omega
  let B : Finset Gamma := G \ R
  let M : ℕ := B.card
  have hMpruned : 9 * h + 7 ≤ 7 * M := by
    dsimp only [M, B]
    exact ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.nine_mul_add_seven_le_seven_mul_card_sdiff
      h G R hRG hG hRcard
  have havgTwo : 4 * h ≤ M * (h + 1) := by
    exact ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.average_two_of_nine_mul_add_one_le_seven_mul
      (h := h) (M := M) (by omega) (by omega)
  let mult : U → ℕ :=
    ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.incidenceMultiplicity B A
  have hsum : M * (h + 1) ≤ ∑ i : U, mult i := by
    exact ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.incidenceMultiplicity_sum_lower
      B A (h + 1) hsize
  have hlower : lowerSix h M ≤ 6 * ∑ i : U, ((mult i).choose 3 : ℚ) := by
    have hJ :=
      ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.thirdMoment_jensen_lower_rat_of_average_two
        mult h M (by omega) hU havgTwo hsum
    dsimp only at hJ
    simpa only [lowerSix] using hJ
  let d := k - 1
  let c := h - 4 - d
  have hd : d ≤ h - 4 := by
    dsimp only [d]
    omega
  have hdc : d + c = h - 4 := by
    dsimp only [c]
    exact Nat.add_sub_of_le hd
  have hupperNat :
      6 * ∑ i : U, (mult i).choose 3 ≤
        d * M * (M - 1) * (M - 2) + 2 * c * M * (M - 1) := by
    have hweighted := weightedTripleSum_upper
      B onLine determinedLine (fun T ↦ (commonCoordinates A T).card)
      d c
      (by simpa only [B] using hpairOn)
      hpairUnique
      (by simpa only [B] using hlineFour)
      (by simpa only [B, d] using hnoncol)
      (by
        intro T hT
        have := hcol T (by simpa only [B] using hT)
        simpa only [hdc] using this)
    have hidentity := sum_choose_incidence_eq_sum_commonCoordinates_card B A
    have hincidence :
        ∑ i : U, (mult i).choose 3 =
          ∑ T ∈ B.powersetCard 3, (commonCoordinates A T).card := by
      simpa only [mult,
        ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.incidenceMultiplicity]
        using hidentity
    rw [hincidence]
    simpa only [M] using hweighted
  have hupper :
      6 * ∑ i : U, ((mult i).choose 3 : ℚ) ≤ bulkUpperSix h M := by
    have hM4 : 4 ≤ M := by omega
    have hM1 : 1 ≤ M := by omega
    have hM2 : 2 ≤ M := by omega
    have hcast :
        (6 * ∑ i : U, ((mult i).choose 3 : ℚ)) ≤
          (d : ℚ) * M * (M - 1) * (M - 2) +
            2 * (c : ℚ) * M * (M - 1) := by
      exact_mod_cast hupperNat
    have hdQ : (d : ℚ) ≤ (h : ℚ) / 4 - 1 := by
      dsimp only [d]
      rw [Nat.cast_sub hk]
      have hrateQ : (4 : ℚ) * k ≤ h := by exact_mod_cast hrate
      linarith
    have hdcQ : (c : ℚ) = (h : ℚ) - 4 - d := by
      have hdcCast : (d : ℚ) + (c : ℚ) = ((h - 4 : ℕ) : ℚ) := by
        exact_mod_cast hdc
      calc
        (c : ℚ) = ((h - 4 : ℕ) : ℚ) - (d : ℚ) := by
          rw [← hdcCast]
          ring
        _ = (h : ℚ) - 4 - d := by
          rw [Nat.cast_sub (by omega : 4 ≤ h), Nat.cast_ofNat]
    have hM4Q : (4 : ℚ) ≤ M := by exact_mod_cast hM4
    have hnonneg : (0 : ℚ) ≤
        (M : ℚ) * ((M : ℚ) - 1) * ((M : ℚ) - 4) := by
      exact mul_nonneg
        (mul_nonneg (by positivity) (sub_nonneg.mpr (by linarith)))
        (sub_nonneg.mpr (by linarith))
    have hcompare :
        (d : ℚ) * M * (M - 1) * (M - 2) +
            2 * (c : ℚ) * M * (M - 1) ≤
          ((h : ℚ) / 4 - 1) * M * (M - 1) * (M - 2) +
            (3 * (h : ℚ) / 2 - 6) * M * (M - 1) := by
      rw [hdcQ]
      nlinarith
    exact hcast.trans (by simpa only [bulkUpperSix] using hcompare)
  have hbulk := nine_mul_le_seven_mul_of_bulk_thirdMoment_bounds
    h M (∑ i : U, ((mult i).choose 3 : ℚ)) (by omega) hlower hupper
  omega

/-! ## Concrete secant geometry -/

/-- In a counterexample, every determined line has core at most `h-4`. -/
theorem jointCore_card_add_four_le_of_card_gt_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 4 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (jointCore dom (u 0) (u 1) line.1 line.2).card + 4 ≤ h := by
  have hcore : 2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 ≤
      h + 4 * (k - 1) := by
    by_contra hnot
    exact largeCore_contradiction_of_card_gt_two_mul
      family (by omega) hk hn (by omega) hline hcard (by omega)
  omega

/-- Distinct determined secant lines have core intersection at most `k-1`. -/
theorem jointCore_inter_card_le_degree_pred
    {dom : ι ↪ F} {k : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    {line line' : LineParameter F}
    (hline : line ∈ lineParameters family)
    (hline' : line' ∈ lineParameters family) (hne : line ≠ line') :
    (jointCore dom (u 0) (u 1) line.1 line.2 ∩
      jointCore dom (u 0) (u 1) line'.1 line'.2).card ≤ k - 1 := by
  have htwo := two_le_pointsOn_card_of_mem_lineParameters family hline
  obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ := Finset.one_lt_card.mp htwo
  have hnsub : ¬ pointsOn family line ⊆ pointsOn family line' := by
    intro hsub
    have hsec := secantParameter_eq_of_mem_pointsOn family line hgamma hbeta hgb
    have hsec' := secantParameter_eq_of_mem_pointsOn family line'
      (hsub hgamma) (hsub hbeta) hgb
    exact hne (hsec.symm.trans hsec')
  simp only [Finset.not_subset] at hnsub
  obtain ⟨theta, htheta, htheta'⟩ := hnsub
  have hthetaG := pointsOn_subset_G family line htheta
  have hthetaEq := (mem_pointsOn_iff family line theta).mp htheta |>.2
  have hthetaNe : family.q theta ≠ line'.1 + C theta * line'.2 := by
    intro heq
    exact htheta' ((mem_pointsOn_iff family line' theta).mpr ⟨hthetaG, heq⟩)
  have hdeg' := lineParameter_degree_lt family hline'
  have hcap := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) hk (family.degree_lt theta hthetaG)
    hdeg'.1 hdeg'.2 hthetaNe
  have hsub :
      jointCore dom (u 0) (u 1) line.1 line.2 ∩
          jointCore dom (u 0) (u 1) line'.1 line'.2 ⊆
        fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
          jointCore dom (u 0) (u 1) line'.1 line'.2 := by
    intro i hi
    rw [Finset.mem_inter] at hi ⊢
    refine ⟨?_, hi.2⟩
    rw [hthetaEq]
    exact jointCore_subset_fullAgreement
      dom (u 0) (u 1) line.1 line.2 theta hi.1
  exact (Finset.card_le_card hsub).trans hcap

/-- Five points plus fresh-fibre packing force the residue-uniform exceptional
core threshold `3*floor(h/4)+2`. -/
theorem exceptional_core_lower_generic
    {h z L : ℕ} (hz : z ≤ h) (hL : 5 ≤ L)
    (hpacking : L * (h + 1 - z) + z ≤ 2 * h) :
    3 * (h / 4) + 2 ≤ z := by
  let q := h / 4
  have hq : 4 * q ≤ h := by
    dsimp only [q]
    omega
  have hc : h + 1 - z + z = h + 1 := Nat.sub_add_cancel (by omega)
  have hmul : 5 * (h + 1 - z) ≤ L * (h + 1 - z) :=
    Nat.mul_le_mul_right _ hL
  omega

/-- The defining ultra fresh-width inequality gives the residue-uniform core
threshold `15*floor(h/16)+1`. -/
theorem ultra_core_lower_generic
    {h z : ℕ} (hz : z ≤ h + 1)
    (hfresh : h + 1 - z ≤ h / 16) :
    15 * (h / 16) + 1 ≤ z := by
  have hq : 16 * (h / 16) ≤ h := by omega
  have hc : h + 1 - z + z = h + 1 := Nat.sub_add_cancel hz
  omega

/-- If the fresh width is larger than `floor(h/16)`, packing permits at most
sixteen points. -/
theorem line_card_le_sixteen_of_fresh_gt_sixteenth
    {h z L : ℕ} (hz : z ≤ h + 1)
    (hfresh : h / 16 < h + 1 - z)
    (hpacking : L * (h + 1 - z) + z ≤ 2 * h) :
    L ≤ 16 := by
  by_contra hnot
  have hL : 17 ≤ L := by omega
  have hmul : 17 * (h + 1 - z) ≤ L * (h + 1 - z) :=
    Nat.mul_le_mul_right _ hL
  have hqUpper : h ≤ 16 * (h / 16) + 15 := by omega
  have hc : h + 1 - z + z = h + 1 := Nat.sub_add_cancel hz
  omega

/-- A collinear selected triple has common agreement equal to the core of its
containing determined line, hence inherits any supplied core ceiling. -/
theorem tripleWeight_le_of_collinear_of_core_ceiling
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (G' : Finset F) (hsubG : G' ⊆ family.G)
    (hcore : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ h - 4)
    (T : Finset F) (hT : T ∈ collinearTriples G' (onFamilyLine family)) :
    tripleWeight family T ≤ h - 4 := by
  obtain ⟨hTG', hTcard, ⟨line, hlineAll⟩⟩ :=
    (mem_collinearTriples_iff G' (onFamilyLine family) T).mp hT
  obtain ⟨gamma, beta, theta, hgb, hgt, hbt, rfl⟩ :=
    Finset.card_eq_three.mp hTcard
  have hgammaG : gamma ∈ family.G := hsubG (hTG' (by simp))
  have hbetaG : beta ∈ family.G := hsubG (hTG' (by simp))
  have hthetaG : theta ∈ family.G := hsubG (hTG' (by simp))
  have hgammaOn : gamma ∈ pointsOn family line := hlineAll gamma (by simp)
  have hbetaOn : beta ∈ pointsOn family line := hlineAll beta (by simp)
  have hthetaOn : theta ∈ pointsOn family line := hlineAll theta (by simp)
  have hline : line ∈ lineParameters family := by
    have hsecant := secantParameter_eq_of_mem_pointsOn
      family line hgammaOn hbetaOn hgb
    rw [← hsecant]
    exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  have hDbound : D.card ≤ h - 4 := hcore line hline
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

/-! ## Canonical-family assembly -/

/-- **Rate-`1/8` canonical rich-point bound.**  At the exact half-predecessor
agreement threshold, every selected bad-scalar family has at most `2h`
members. -/
theorem badScalarRichPointFamily_card_le_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hh : 1699 ≤ h) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold : ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 4 * k ≤ h) :
    family.G.card ≤ 2 * h := by
  classical
  by_contra hnot
  have hcard : 2 * h < family.G.card := by omega
  let core : LineParameter F → Finset ι := fun line ↦
    jointCore dom (u 0) (u 1) line.1 line.2
  let E : Finset (LineParameter F) :=
    (lineParameters family).filter fun line ↦ 5 ≤ (pointsOn family line).card
  let Q : Finset (LineParameter F) :=
    E.filter fun line ↦ h + 1 - (core line).card ≤ h / 16
  let R : Finset F := E.biUnion (pointsOn family)
  let A : F → Finset ι := selectedAgreements family
  have hcoreCeiling : ∀ line ∈ lineParameters family,
      (core line).card + 4 ≤ h := by
    intro line hline
    simpa only [core] using
      jointCore_card_add_four_le_of_card_gt_two_mul
        family hk hn hthreshold hrate hcard hline
  have hpacking : ∀ line ∈ lineParameters family,
      (pointsOn family line).card * (h + 1 - (core line).card) +
        (core line).card ≤ 2 * h := by
    intro line hline
    have hraw := pointsOn_card_mul_max_add_core_le family hline
    rw [hthreshold, hn] at hraw
    have hz := hcoreCeiling line hline
    have hone : 1 ≤ h + 1 - (core line).card := by omega
    rw [max_eq_right hone] at hraw
    simpa only [core] using hraw
  have hEcore : ∀ line ∈ E,
      3 * (h / 4) + 2 ≤ (core line).card := by
    intro line hlineE
    have hdata : line ∈ lineParameters family ∧
        5 ≤ (pointsOn family line).card := by
      simpa only [E, Finset.mem_filter] using hlineE
    exact exceptional_core_lower_generic
      (by have := hcoreCeiling line hdata.1; omega)
      hdata.2 (hpacking line hdata.1)
  have hinter : ∀ line ∈ E, ∀ line' ∈ E, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1 := by
    intro line hline line' hline' hne
    have hlineData : line ∈ lineParameters family :=
      (Finset.mem_filter.mp hline).1
    have hlineData' : line' ∈ lineParameters family :=
      (Finset.mem_filter.mp hline').1
    simpa only [core] using
      jointCore_inter_card_le_degree_pred
        family hk hlineData hlineData' hne
  have hEcard : E.card ≤ 15 :=
    exceptional_core_family_card_le_fifteen_generic
      h k hh hk hrate hn E core hEcore hinter
  have hQE : Q ⊆ E := Finset.filter_subset _ _
  have hQcore : ∀ line ∈ Q,
      15 * (h / 16) + 1 ≤ (core line).card := by
    intro line hlineQ
    have hdata := Finset.mem_filter.mp hlineQ
    have hlineParam : line ∈ lineParameters family :=
      (Finset.mem_filter.mp hdata.1).1
    exact ultra_core_lower_generic
      (by have := hcoreCeiling line hlineParam; omega) hdata.2
  have hQinter : ∀ line ∈ Q, ∀ line' ∈ Q, line ≠ line' →
      (core line ∩ core line').card ≤ k - 1 := by
    intro line hline line' hline' hne
    exact hinter line (hQE hline) line' (hQE hline') hne
  have hQcard : Q.card ≤ 3 :=
    ultra_core_family_card_le_three_generic
      h k hh hk hrate hn Q core hQcore hQinter
  have hultra : ∀ line ∈ Q,
      5 * (pointsOn family line).card ≤ h + 4 := by
    intro line hlineQ
    have hlineE := hQE hlineQ
    have hlineParam : line ∈ lineParameters family :=
      (Finset.mem_filter.mp hlineE).1
    exact global_core_ceiling_line_budget
      (hcoreCeiling line hlineParam) (hpacking line hlineParam)
  have hordinary : ∀ line ∈ E \ Q,
      (pointsOn family line).card ≤ 16 := by
    intro line hline
    have hlineE := (Finset.mem_sdiff.mp hline).1
    have hlineNotQ := (Finset.mem_sdiff.mp hline).2
    have hlineParam : line ∈ lineParameters family :=
      (Finset.mem_filter.mp hlineE).1
    have hfresh : h / 16 < h + 1 - (core line).card := by
      by_contra hnotFresh
      apply hlineNotQ
      exact Finset.mem_filter.mpr ⟨hlineE, by omega⟩
    exact line_card_le_sixteen_of_fresh_gt_sixteenth
      (by have := hcoreCeiling line hlineParam; omega)
      hfresh (hpacking line hlineParam)
  have hRcard : 7 * R.card ≤ 5 * h := by
    exact ArkLib.ProximityGap.Frontier.R387RateEighthPruning.exceptional_biUnion_seven_mul_card_le_five_mul
      h (by omega) E Q (pointsOn family) hQE hEcard hQcard hultra hordinary
  have hRG : R ⊆ family.G := by
    intro gamma hgamma
    obtain ⟨line, hline, hgammaLine⟩ := Finset.mem_biUnion.mp hgamma
    exact pointsOn_subset_G family line hgammaLine
  have hsize : ∀ gamma ∈ family.G \ R,
      h + 1 ≤ (A gamma).card := by
    intro gamma hgamma
    have hgammaG := (Finset.mem_sdiff.mp hgamma).1
    simpa only [A, selectedAgreements, hthreshold] using
      family.threshold_le gamma hgammaG
  have hpairOn : ∀ x ∈ family.G \ R, ∀ y ∈ family.G \ R, x ≠ y →
      onFamilyLine family (secantParameter family x y) x ∧
        onFamilyLine family (secantParameter family x y) y := by
    intro x hx y hy hxy
    have hxG := (Finset.mem_sdiff.mp hx).1
    have hyG := (Finset.mem_sdiff.mp hy).1
    exact ⟨first_point_mem_pointsOn_secant family hxG,
      second_point_mem_pointsOn_secant family hyG hxy⟩
  have hpairUnique : ∀ line x y, x ≠ y →
      onFamilyLine family line x → onFamilyLine family line y →
        line = secantParameter family x y := by
    intro line x y hxy hx hy
    exact (secantParameter_eq_of_mem_pointsOn family line hx hy hxy).symm
  have hlineFour : ∀ line,
      (linePoints (family.G \ R) (onFamilyLine family) line).card ≤ 4 := by
    intro line
    by_cases hlineE : line ∈ E
    · have hempty :
          linePoints (family.G \ R) (onFamilyLine family) line = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro gamma hgamma
        have hdata := Finset.mem_filter.mp hgamma
        have hgammaOn : gamma ∈ pointsOn family line := hdata.2
        have hgammaR : gamma ∈ R :=
          Finset.mem_biUnion.mpr ⟨line, hlineE, hgammaOn⟩
        exact (Finset.mem_sdiff.mp hdata.1).2 hgammaR
      rw [hempty]
      simp
    · have hpoints : (pointsOn family line).card ≤ 4 := by
        by_contra hnotPoints
        have hfive : 5 ≤ (pointsOn family line).card := by omega
        have htwo : 1 < (pointsOn family line).card := by omega
        obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ :=
          Finset.one_lt_card.mp htwo
        have hgammaG := pointsOn_subset_G family line hgamma
        have hbetaG := pointsOn_subset_G family line hbeta
        have hsecant := secantParameter_eq_of_mem_pointsOn
          family line hgamma hbeta hgb
        have hlineParam : line ∈ lineParameters family := by
          rw [← hsecant]
          exact secantParameter_mem_lineParameters family hgammaG hbetaG hgb
        exact hlineE (Finset.mem_filter.mpr ⟨hlineParam, hfive⟩)
      apply (Finset.card_le_card ?_).trans hpoints
      intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2
  have hnoncol : ∀ T ∈ (family.G \ R).powersetCard 3,
      ¬ Collinear (onFamilyLine family) T →
        (commonCoordinates A T).card ≤ k - 1 := by
    intro T hT hnotCol
    have hTG : T ∈ family.G.powersetCard 3 := by
      rw [Finset.mem_powersetCard] at hT ⊢
      exact ⟨fun gamma hgamma ↦
        (Finset.mem_sdiff.mp (hT.1 hgamma)).1, hT.2⟩
    simpa only [A, tripleWeight] using
      tripleWeight_le_degree_pred_of_not_collinear
        family hk T hTG hnotCol
  have hcol : ∀ T ∈ collinearTriples (family.G \ R) (onFamilyLine family),
      (commonCoordinates A T).card ≤ h - 4 := by
    intro T hT
    have hsub : family.G \ R ⊆ family.G := Finset.sdiff_subset
    have hcore' : ∀ line ∈ lineParameters family,
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ h - 4 := by
      intro line hline
      have := hcoreCeiling line hline
      simpa only [core] using (show
        (core line).card ≤ h - 4 by omega)
    simpa only [A, tripleWeight] using
      tripleWeight_le_of_collinear_of_core_ceiling
        family (family.G \ R) hsub hcore' T hT
  have hbound := card_le_two_mul_of_pruned_geometry
    h k hh hk hrate hn family.G R A
    (onFamilyLine family) (secantParameter family)
    hRG hRcard hsize hpairOn hpairUnique hlineFour hnoncol hcol
  omega

/-! ## Literal bad-event wrappers -/

/-- The canonical choice of one rich point above every bad scalar has at most
the code length many members. -/
theorem canonicalRichPointFamily_card_le_two_mul
    (dom : ι ↪ F) {k h : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hh : 1699 ≤ h) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 4 * k ≤ h) :
    (canonicalBadScalarRichPointFamily dom delta u hk).G.card ≤ 2 * h :=
  badScalarRichPointFamily_card_le_two_mul
    (canonicalBadScalarRichPointFamily dom delta u hk)
    hh hk hn hthreshold hrate

/-- Literal bad-event filter form at every radius whose agreement ceiling is
`h+1`. -/
theorem badScalar_filter_card_le_two_mul
    (dom : ι ↪ F) {k h : ℕ} (delta : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (hh : 1699 ≤ h) (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 4 * k ≤ h) :
    (Finset.univ.filter fun gamma : F ↦
      mcaEvent ((ReedSolomon.code dom k : Set (ι → F)))
        delta (u 0) (u 1) gamma).card ≤ 2 * h := by
  simpa only [canonicalBadScalarRichPointFamily, badScalars] using
    canonicalRichPointFamily_card_le_two_mul
      dom delta u hh hk hn hthreshold hrate

/-- Operational half-predecessor form for an arbitrary even code length. -/
theorem canonical_halfPredecessor_card_le_length
    {n h k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 2 * h) (hh : 1699 ≤ h) (hk : 1 ≤ k)
    (hrate : 8 * k ≤ n)
    (u : WordStack F (Fin 2) (Fin n)) :
    (canonicalBadScalarRichPointFamily dom (k := k)
      (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
      u hk).G.card ≤ n := by
  have hcardFin : Fintype.card (Fin n) = 2 * h := by simp [hn]
  have hthreshold := halfPredecessor_ceiling_agreement_eq hn (by omega)
  have hbound := canonicalRichPointFamily_card_le_two_mul
    dom
    (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
    u hh hk hcardFin (by simpa only [Fintype.card_fin] using hthreshold)
    (by omega)
  simpa only [hn] using hbound

/-- **Literal uniform rate-`1/8` predecessor bad-count theorem.**  For every
received affine word and every even length `n=2h` with `h≥1699`, at most `n`
scalars trigger the MCA bad event whenever `8k≤n`. -/
theorem halfPredecessor_badScalar_filter_card_le_length
    {n h k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 2 * h) (hh : 1699 ≤ h) (hk : 1 ≤ k)
    (hrate : 8 * k ≤ n)
    (u : WordStack F (Fin 2) (Fin n)) :
    (Finset.univ.filter fun gamma : F ↦
      mcaEvent ((ReedSolomon.code dom k : Set (Fin n → F)))
        (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius n)
        (u 0) (u 1) gamma).card ≤ n := by
  simpa only [canonicalBadScalarRichPointFamily, badScalars] using
    canonical_halfPredecessor_card_le_length dom hn hh hk hrate u

/-- Prize-length specialization (`n=2^30`, `h=2^29`). -/
theorem halfPredecessor_badScalar_filter_card_le_two_pow_thirty
    {k : ℕ} (dom : Fin (2 ^ 30) ↪ F) (hk : 1 ≤ k)
    (hrate : 8 * k ≤ 2 ^ 30)
    (u : WordStack F (Fin 2) (Fin (2 ^ 30))) :
    (Finset.univ.filter fun gamma : F ↦
      mcaEvent ((ReedSolomon.code dom k : Set (Fin (2 ^ 30) → F)))
        (ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius (2 ^ 30))
        (u 0) (u 1) gamma).card ≤ 2 ^ 30 := by
  apply halfPredecessor_badScalar_filter_card_le_length
    (h := 2 ^ 29) dom
  · norm_num [pow_succ]
  · norm_num
  · exact hk
  · exact hrate

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.exceptional_core_family_card_le_fifteen_generic
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.ultra_core_family_card_le_three_generic
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.card_le_two_mul_of_pruned_geometry
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.jointCore_inter_card_le_degree_pred
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.badScalarRichPointFamily_card_le_two_mul
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.halfPredecessor_badScalar_filter_card_le_length
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.halfPredecessor_badScalar_filter_card_le_two_pow_thirty
