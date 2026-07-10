/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R387RateEighthPruning
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorThirdMomentUpper

/-!
# R387: the pruned third-moment contradiction at rate `1/8`

The Johnson pruning theorem removes at most `5h/7` selected points from a
hypothetical family of more than `2h` half-predecessor bad scalars.  The surviving
family therefore has size `M > 9h/7`, and every secant line has at most four
surviving points.

This file supplies the two remaining abstract pieces:

* Jensen's lower bound for the third incidence moment under the exact minimal
  hypothesis that the average multiplicity is at least two.  The older
  half-predecessor Jensen wrapper assumed `M > 2h`; pruning makes that hypothesis
  unavailable even though the average is still much larger than two.
* the exact rational inequality separating the Jensen lower bound from the
  line-corrected triple upper bound at rate `1/8`.

The final theorem `card_le_thirtyTwo_mul_of_pruned_geometry` is an abstract consumer.
It does not mention fields or polynomials: a concrete secant configuration only has
to provide the removable set and the triple-codegree hypotheses.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment

open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper

/-! ## Jensen with the correct post-pruning hypothesis -/

/-- The descending Pochhammer polynomial of order three is the usual cubic. -/
private theorem descPochhammer_three_eval (x : ℝ) :
    (descPochhammer ℝ 3).eval x = x * (x - 1) * (x - 2) := by
  norm_num [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ]

/-- **Third-moment Jensen from average at least two.**  On `2h` coordinates,
total incidence at least `N(h+1)` gives the usual cubic lower bound, provided
`4h <= N(h+1)`, which is exactly the assertion that the comparison average is
at least two. -/
theorem thirdMoment_jensen_lower_rat_of_average_two
    {U : Type*} [Fintype U] (mult : U → ℕ) (h N : ℕ)
    (hh : 0 < h) (hcard : Fintype.card U = 2 * h)
    (havgTwo : 4 * h ≤ N * (h + 1))
    (hsum : N * (h + 1) ≤ ∑ i, mult i) :
    let a : ℚ := (N : ℚ) * ((h : ℚ) + 1) / (2 * (h : ℚ))
    2 * (h : ℚ) * a * (a - 1) * (a - 2) ≤
      6 * ∑ i, ((mult i).choose 3 : ℚ) := by
  let den : ℝ := 2 * (h : ℝ)
  let weight : U → ℝ := fun _ ↦ 1 / den
  let avg : ℝ := ∑ i, weight i * (mult i : ℝ)
  let target : ℝ := (N : ℝ) * ((h : ℝ) + 1) / den
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hden : 0 < den := by positivity
  have hcardR : (Fintype.card U : ℝ) = den := by
    simp only [den]
    exact_mod_cast hcard
  have hw0 : ∀ i ∈ (Finset.univ : Finset U), 0 ≤ weight i := by
    intro i hi
    simp only [weight]
    positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset U), weight i = 1 := by
    simp only [weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcardR]
    field_simp
  have havg_eq : avg = (∑ i, (mult i : ℝ)) / den := by
    simp only [avg, weight]
    rw [← Finset.mul_sum]
    simp [div_eq_mul_inv, mul_comm]
  have hsumR :
      (N : ℝ) * ((h : ℝ) + 1) ≤ ∑ i, (mult i : ℝ) := by
    exact_mod_cast hsum
  have htarget_avg : target ≤ avg := by
    change (N : ℝ) * ((h : ℝ) + 1) / den ≤ avg
    rw [havg_eq]
    exact (div_le_div_iff_of_pos_right hden).2 hsumR
  have htarget_two : (2 : ℝ) ≤ target := by
    have havgTwoR : (4 : ℝ) * (h : ℝ) ≤
        (N : ℝ) * ((h : ℝ) + 1) := by
      exact_mod_cast havgTwo
    change (2 : ℝ) ≤ (N : ℝ) * ((h : ℝ) + 1) / den
    apply (le_div_iff₀ hden).2
    dsimp only [den]
    linarith
  have havg_two : (2 : ℝ) ≤ avg := htarget_two.trans htarget_avg
  have hjensen := descPochhammer_eval_div_factorial_le_sum_choose
    (n := 3) (by norm_num) (t := (Finset.univ : Finset U)) mult weight hw0 hw1 (by
      norm_num
      exact havg_two)
  have hmono :
      (descPochhammer ℝ 3).eval target ≤ (descPochhammer ℝ 3).eval avg :=
    monotoneOn_descPochhammer_eval 3 (by
      simp only [Set.mem_Ici]
      norm_num
      linarith) (by
      simp only [Set.mem_Ici]
      norm_num
      linarith) htarget_avg
  have hjensen' :
      (descPochhammer ℝ 3).eval avg / 6 ≤
        (∑ i, ((mult i).choose 3 : ℝ)) / den := by
    change (descPochhammer ℝ 3).eval avg / 6 ≤ _
    calc
      (descPochhammer ℝ 3).eval avg / 6 ≤
          ∑ i, weight i * ((mult i).choose 3 : ℝ) := by
            simpa only [Nat.factorial, Nat.cast_ofNat] using hjensen
      _ = (∑ i, ((mult i).choose 3 : ℝ)) / den := by
        simp only [weight, one_div_mul_eq_div, Finset.sum_div]
  have hreal :
      den * target * (target - 1) * (target - 2) ≤
        6 * ∑ i, ((mult i).choose 3 : ℝ) := by
    calc
      den * target * (target - 1) * (target - 2) =
          den * (descPochhammer ℝ 3).eval target := by
            rw [descPochhammer_three_eval]
            ring
      _ ≤ den * (descPochhammer ℝ 3).eval avg := by gcongr
      _ ≤ 6 * ∑ i, ((mult i).choose 3 : ℝ) := by
        have hcross :=
          (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 6) hden).1 hjensen'
        nlinarith
  dsimp only [den, target] at hreal
  dsimp only
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  simpa only [Nat.cast_sum] using hreal

/-! ## First-moment incidence identity -/

/-- Multiplicity of a coordinate in a finite set family. -/
def incidenceMultiplicity
    {U Gamma : Type*} [DecidableEq U] [DecidableEq Gamma]
    (G : Finset Gamma) (A : Gamma → Finset U) (i : U) : ℕ :=
  (G.filter fun gamma ↦ i ∈ A gamma).card

/-- Total coordinate multiplicity equals the sum of the member cardinalities. -/
theorem sum_incidenceMultiplicity_eq_sum_card
    {U Gamma : Type*} [Fintype U] [DecidableEq U] [DecidableEq Gamma]
    (G : Finset Gamma) (A : Gamma → Finset U) :
    ∑ i : U, incidenceMultiplicity G A i =
      ∑ gamma ∈ G, (A gamma).card := by
  classical
  simp only [incidenceMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gamma hgamma
  rw [Finset.sum_boole]
  simp

/-- Uniform largeness of the members supplies the total-incidence hypothesis
used by Jensen. -/
theorem incidenceMultiplicity_sum_lower
    {U Gamma : Type*} [Fintype U] [DecidableEq U] [DecidableEq Gamma]
    (G : Finset Gamma) (A : Gamma → Finset U) (t : ℕ)
    (hsize : ∀ gamma ∈ G, t ≤ (A gamma).card) :
    G.card * t ≤ ∑ i : U, incidenceMultiplicity G A i := by
  rw [sum_incidenceMultiplicity_eq_sum_card]
  calc
    G.card * t = ∑ _gamma ∈ G, t := by simp
    _ ≤ ∑ gamma ∈ G, (A gamma).card := Finset.sum_le_sum hsize

/-! ## Exact rate-`1/8` numeric gap -/

/-- Six times the Jensen lower bound with `h=16m`. -/
def lowerSix (m M : ℕ) : ℚ :=
  let avg : ℚ := (M : ℚ) * (16 * (m : ℚ) + 1) / (32 * (m : ℚ))
  32 * (m : ℚ) * avg * (avg - 1) * (avg - 2)

/-- Six times the line-corrected upper bound.  The noncollinear codegree cap
is `4m-1`; the collinear excess cap is `12m-3`. -/
def upperSix (m M : ℕ) : ℚ :=
  (4 * (m : ℚ) - 1) * (M : ℚ) * ((M : ℚ) - 1) * ((M : ℚ) - 2) +
    2 * (12 * (m : ℚ) - 3) * (M : ℚ) * ((M : ℚ) - 1)

/-- Four times the gap after removing its positive factor `M`. -/
def gapFour (m M : ℕ) : ℚ :=
  (7 + 3 / (16 * (m : ℚ)) + 1 / (256 * (m : ℚ) ^ 2)) * (M : ℚ) ^ 2 -
    (144 * (m : ℚ) + 3 / (8 * (m : ℚ))) * (M : ℚ) +
    192 * (m : ℚ) - 8

/-- Exact factorization of the pruned third-moment gap. -/
theorem four_mul_lowerSix_sub_upperSix_eq (m M : ℕ) (hm : 0 < m) :
    4 * (lowerSix m M - upperSix m M) = (M : ℚ) * gapFour m M := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [lowerSix, upperSix, gapFour]
  push_cast
  field_simp [hmQ]
  ring

/-- The gap factor is positive as soon as `M > 9h/7`, written without
division as `144m+1 <= 7M`. -/
theorem gapFour_pos (m M : ℕ) (hm : 1 ≤ m)
    (hM : 144 * m + 1 ≤ 7 * M) :
    0 < gapFour m M := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (show 0 < m by omega)
  have hMQ : (144 : ℚ) * m + 1 ≤ 7 * M := by exact_mod_cast hM
  have hfrac : 3 / (8 * (m : ℚ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have hm1Q : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    linarith
  have hMpos : (0 : ℚ) < (M : ℚ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hcoef : (7 : ℚ) ≤
      7 + 3 / (16 * (m : ℚ)) + 1 / (256 * (m : ℚ) ^ 2) := by
    have h1 : (0 : ℚ) ≤ 3 / (16 * (m : ℚ)) := by positivity
    have h2 : (0 : ℚ) ≤ 1 / (256 * (m : ℚ) ^ 2) := by positivity
    linarith
  have hlead :
      144 * (m : ℚ) + 3 / (8 * (m : ℚ)) <
        (7 + 3 / (16 * (m : ℚ)) + 1 / (256 * (m : ℚ) ^ 2)) * (M : ℚ) := by
    calc
      144 * (m : ℚ) + 3 / (8 * (m : ℚ)) <
          144 * (m : ℚ) + 1 := by linarith
      _ ≤ 7 * (M : ℚ) := hMQ
      _ ≤ (7 + 3 / (16 * (m : ℚ)) +
          1 / (256 * (m : ℚ) ^ 2)) * (M : ℚ) := by
            exact mul_le_mul_of_nonneg_right hcoef hMpos.le
  have htail : (0 : ℚ) < 192 * (m : ℚ) - 8 := by
    have hm1Q : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    linarith
  simp only [gapFour]
  nlinarith [mul_pos hMpos (sub_pos.mpr hlead)]

/-- **Strict pruned third-moment separation.** -/
theorem upperSix_lt_lowerSix (m M : ℕ) (hm : 1 ≤ m)
    (hM : 144 * m + 1 ≤ 7 * M) :
    upperSix m M < lowerSix m M := by
  have hid := four_mul_lowerSix_sub_upperSix_eq m M (by omega)
  have hgap := gapFour_pos m M hm hM
  have hMpos : (0 : ℚ) < (M : ℚ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  nlinarith [mul_pos hMpos hgap]

/-! ## Pruned cardinal arithmetic -/

/-- Removing at most `5h/7` points from a family of size at least `2h+1`
leaves strictly more than `9h/7` points. -/
theorem nine_mul_add_seven_le_seven_mul_card_sdiff
    {Gamma : Type*} [DecidableEq Gamma]
    (h : ℕ) (G R : Finset Gamma) (hRG : R ⊆ G)
    (hG : 2 * h + 1 ≤ G.card) (hR : 7 * R.card ≤ 5 * h) :
    9 * h + 7 ≤ 7 * (G \ R).card := by
  rw [Finset.card_sdiff_of_subset hRG]
  have hRcard : R.card ≤ G.card := Finset.card_le_card hRG
  omega

/-- The post-pruning size lower bound forces average multiplicity at least two. -/
theorem average_two_of_nine_mul_add_one_le_seven_mul
    {h M : ℕ} (hh : 3 ≤ h) (hM : 9 * h + 1 ≤ 7 * M) :
    4 * h ≤ M * (h + 1) := by
  have hmul := Nat.mul_le_mul_right (h + 1) hM
  nlinarith

/-! ## Abstract production-rate consumer -/

/-- **Abstract half-predecessor incidence bound at rate at most `1/8`.**

Let the coordinate universe have size `32m=2h`, where `h=16m` and `m>=128`.
Assume `R` is a removable subset occupying at most `5h/7`.  On the remaining
family, every agreement set has size at least `h+1`, noncollinear triples have
codegree at most `4m-1`, collinear triples have codegree at most `16m-4`, and
there are at most two collinear third points above every ordered pair.  Then the
original family has size at most `32m`.

The last cardinal hypothesis is exactly what uniqueness of secant lines plus
the post-pruning line-size bound `<=4` supplies. -/
theorem card_le_thirtyTwo_mul_of_pruned_geometry
    {U Gamma Line : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq Gamma] [DecidableEq Line]
    (m : ℕ) (hm : 128 ≤ m) (hU : Fintype.card U = 32 * m)
    (G R : Finset Gamma) (A : Gamma → Finset U)
    (onLine : Line → Gamma → Prop) (determinedLine : Gamma → Gamma → Line)
    (hRG : R ⊆ G) (hRcard : 7 * R.card ≤ 80 * m)
    (hsize : ∀ gamma ∈ G \ R, 16 * m + 1 ≤ (A gamma).card)
    (hpairOn : ∀ x ∈ G \ R, ∀ y ∈ G \ R, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hlineFour : ∀ ell, (linePoints (G \ R) onLine ell).card ≤ 4)
    (hnoncol : ∀ T ∈ (G \ R).powersetCard 3, ¬ Collinear onLine T →
      (commonCoordinates A T).card ≤ 4 * m - 1)
    (hcol : ∀ T ∈ collinearTriples (G \ R) onLine,
      (commonCoordinates A T).card ≤ (4 * m - 1) + (12 * m - 3)) :
    G.card ≤ 32 * m := by
  classical
  by_contra hnot
  have hG : 32 * m + 1 ≤ G.card := by omega
  let B : Finset Gamma := G \ R
  let M : ℕ := B.card
  have hpruned : 144 * m + 7 ≤ 7 * M := by
    dsimp only [M, B]
    have := nine_mul_add_seven_le_seven_mul_card_sdiff
      (16 * m) G R hRG (by omega) hRcard
    nlinarith
  have hM : 144 * m + 1 ≤ 7 * M := by omega
  have havgTwo : 64 * m ≤ M * (16 * m + 1) := by
    exact average_two_of_nine_mul_add_one_le_seven_mul
      (h := 16 * m) (M := M) (by omega) (by nlinarith [hM])
  have hsum : M * (16 * m + 1) ≤
      ∑ i : U, incidenceMultiplicity B A i := by
    exact incidenceMultiplicity_sum_lower B A (16 * m + 1) (by
      intro gamma hgamma
      exact hsize gamma hgamma)
  have hlower : lowerSix m M ≤
      6 * ∑ i : U, ((incidenceMultiplicity B A i).choose 3 : ℚ) := by
    have hJ := thirdMoment_jensen_lower_rat_of_average_two
      (fun i ↦ incidenceMultiplicity B A i) (16 * m) M
      (by omega) (by simpa [mul_assoc] using hU) havgTwo hsum
    simpa only [lowerSix] using hJ
  have hupperNat :
      6 * ∑ i : U, (incidenceMultiplicity B A i).choose 3 ≤
        (4 * m - 1) * M * (M - 1) * (M - 2) +
          2 * (12 * m - 3) * M * (M - 1) := by
    have hweighted := weightedTripleSum_upper
      B onLine determinedLine (fun T ↦ (commonCoordinates A T).card)
      (4 * m - 1) (12 * m - 3)
      (by simpa only [B] using hpairOn)
      hpairUnique
      (by simpa only [B] using hlineFour)
      (by simpa only [B] using hnoncol)
      (by simpa only [B] using hcol)
    have hidentity := sum_choose_incidence_eq_sum_commonCoordinates_card B A
    have hincidence :
        ∑ i : U, (incidenceMultiplicity B A i).choose 3 =
          ∑ T ∈ B.powersetCard 3, (commonCoordinates A T).card := by
      simpa only [incidenceMultiplicity] using hidentity
    rw [hincidence]
    simpa only [M] using hweighted
  have hupper :
      6 * ∑ i : U, ((incidenceMultiplicity B A i).choose 3 : ℚ) ≤
        upperSix m M := by
    have hcast :
        (6 * ∑ i : U, (incidenceMultiplicity B A i).choose 3 : ℚ) ≤
          ((4 * m - 1) * M * (M - 1) * (M - 2) +
            2 * (12 * m - 3) * M * (M - 1) : ℕ) := by
      exact_mod_cast hupperNat
    have hm4 : 1 ≤ 4 * m := by omega
    have hm12 : 3 ≤ 12 * m := by omega
    have hM1 : 1 ≤ M := by omega
    have hM2 : 2 ≤ M := by omega
    rw [Nat.cast_sub hm4, Nat.cast_sub hm12, Nat.cast_sub hM1,
      Nat.cast_sub hM2] at hcast
    simpa only [upperSix] using hcast
  have hgap := upperSix_lt_lowerSix m M (by omega) hM
  linarith

end ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment

#print axioms
  ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.thirdMoment_jensen_lower_rat_of_average_two
#print axioms
  ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.upperSix_lt_lowerSix
#print axioms
  ArkLib.ProximityGap.Frontier.R387RateEighthPrunedMoment.card_le_thirtyTwo_mul_of_pruned_geometry
