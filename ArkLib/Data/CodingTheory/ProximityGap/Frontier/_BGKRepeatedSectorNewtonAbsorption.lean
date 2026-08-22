/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionRigidity

/-!
# Newton--Möbius decomposition and absorption of the repeated depth-seven sector

Let `w : H → ℂ` be the additive phase at one nonzero frequency and put

`p_j = ∑_{x ∈ H} w(x)^j`.

The Fourier transform over ordered **injective** seven-tuples is `7! e₇(w(H))`.  Newton's
identities give the exact partition-lattice (equivalently permutation-cycle) expansion

`D₇ = p₁⁷ - 21 p₂p₁⁵ + 105 p₂²p₁³ + 70 p₃p₁⁴ + ... + 720 p₇`.

For a dyadic subgroup, `-H = H`, so the repeated-coordinate Fourier integrand is

`p₁¹⁴ - D₇²`.

The first term after cancellation is exactly `42 p₂p₁¹²`: there are `21` choices of a repeated
pair on either side.  The next layer is

`-651 p₂²p₁¹⁰ - 140 p₃p₁¹¹`,

and every remaining monomial has at most eleven factors.  This is the exact Möbius explanation of
the shifted thirteenth moment in `_BGKWeightedCollisionMoment.lean`.

The companion exact probe groups the absolute coefficients by factor count `k`:

`(A₁₃,...,A₂) = (42,791,8820,64743,328986,1184153,3034920,5482456,
                  6787872,5450256,2540160,518400)`.

Generalized Hölder bounds a `k`-factor shifted moment by the `k/14` power of the full fourteenth
moment.  At `|H|=2^30`, this graded polynomial is less than `1/779` of the coefficient-`2^18`
barrier if one discards the favorable `2^18` fractional powers, and less than `138·q|H|^7` when
they are retained.  Thus repeated coordinates are a contractive lower-order term, not a second
independent depth-seven conjecture.  The final barrier lemmas make that bootstrap noncircular:
an injective allowance `126871·q|H|^7`, a repeated allowance `138·q|H|^7`, and any secant slope
at most `1/1024` close the exact slack `127009·q|H|^7`.

This file proves the Newton identity, the two leading Möbius layers, the integer absorption
certificate, and the abstract noncircular barrier.  It does not prove the analytic generalized
Hölder socket or the injective packet bound.  Issue #466.
-/

set_option autoImplicit false

open Finset BigOperators
open ArkLib.ProximityGap.MomentCollisionRigidity

namespace ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption

/-- Production field-size integer, repeated locally so this file does not depend on another
scratch-lane module. -/
def productionQ : ℕ := 2 ^ 30 * (2 ^ 128 + 192) + 1

/-! ## Exact Newton transform -/

/-- Power sum of a finite phase family.  For `w x = ψ(bx)`, this is `η_{jb}`. -/
noncomputable def phasePowerSum {ι : Type*} [Fintype ι] (w : ι → ℂ) (j : ℕ) : ℂ :=
  ∑ i, w i ^ j

/-- Ordered-injective seven-tuple transform, represented as `7!` times the seventh elementary
symmetric polynomial. -/
noncomputable def injectiveSevenTransform {ι : Type*} [Fintype ι] (w : ι → ℂ) : ℂ :=
  (Nat.factorial 7 : ℂ) * (Finset.univ.val.map w).esymm 7

/-- The explicit cycle-index/Newton polynomial for ordered injective seven-tuples. -/
def distinctSevenPolynomial (p1 p2 p3 p4 p5 p6 p7 : ℂ) : ℂ :=
  p1 ^ 7 - 21 * p1 ^ 5 * p2 + 105 * p1 ^ 3 * p2 ^ 2 + 70 * p1 ^ 4 * p3
    - 105 * p1 * p2 ^ 3 - 420 * p1 ^ 2 * p2 * p3 - 210 * p1 ^ 3 * p4
    + 210 * p2 ^ 2 * p3 + 280 * p1 * p3 ^ 2 + 630 * p1 * p2 * p4
    + 504 * p1 ^ 2 * p5 - 420 * p3 * p4 - 504 * p2 * p5
    - 840 * p1 * p6 + 720 * p7

/-- **Exact depth-seven Newton identity.**  This is Möbius inversion on the partition lattice in
power-sum coordinates; no characteristic issue arises because the target ring is `ℂ`. -/
theorem injectiveSevenTransform_eq_distinctSevenPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℂ) :
    injectiveSevenTransform w =
      distinctSevenPolynomial
        (phasePowerSum w 1) (phasePowerSum w 2) (phasePowerSum w 3)
        (phasePowerSum w 4) (phasePowerSum w 5) (phasePowerSum w 6)
        (phasePowerSum w 7) := by
  classical
  have h1 := multiset_newton w 1
  have h2 := multiset_newton w 2
  have h3 := multiset_newton w 3
  have h4 := multiset_newton w 4
  have h5 := multiset_newton w 5
  have h6 := multiset_newton w 6
  have h7 := multiset_newton w 7
  have ha1 : (Finset.antidiagonal 1).filter (fun a => a.1 < 1) = {(0, 1)} := by
    decide
  have ha2 : (Finset.antidiagonal 2).filter (fun a => a.1 < 2) =
      {(0, 2), (1, 1)} := by decide
  have ha3 : (Finset.antidiagonal 3).filter (fun a => a.1 < 3) =
      {(0, 3), (1, 2), (2, 1)} := by decide
  have ha4 : (Finset.antidiagonal 4).filter (fun a => a.1 < 4) =
      {(0, 4), (1, 3), (2, 2), (3, 1)} := by decide
  have ha5 : (Finset.antidiagonal 5).filter (fun a => a.1 < 5) =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} := by decide
  have ha6 : (Finset.antidiagonal 6).filter (fun a => a.1 < 6) =
      {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1)} := by decide
  have ha7 : (Finset.antidiagonal 7).filter (fun a => a.1 < 7) =
      {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)} := by decide
  rw [ha1] at h1
  rw [ha2] at h2
  rw [ha3] at h3
  rw [ha4] at h4
  rw [ha5] at h5
  rw [ha6] at h6
  rw [ha7] at h7
  have he0 : (Finset.univ.val.map w).esymm 0 = (1 : ℂ) := by
    simp [Multiset.esymm]
  norm_num [Finset.sum_insert, psumMs, phasePowerSum] at h1 h2 h3 h4 h5 h6 h7
  rw [he0] at h1 h2 h3 h4 h5 h6 h7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  ring_nf at h1 h2 h3 h4 h5 h6 h7
  let E : ℕ → ℂ := fun k => (Finset.univ.val.map w).esymm k
  have h1' : E 1 = phasePowerSum w 1 := by
    simpa [E, phasePowerSum] using h1
  have h2' : 2 * E 2 = E 1 * phasePowerSum w 1 - phasePowerSum w 2 := by
    simpa [E, phasePowerSum, mul_comm] using h2
  have h3' : 3 * E 3 = E 2 * phasePowerSum w 1 -
      E 1 * phasePowerSum w 2 + phasePowerSum w 3 := by
    simpa [E, phasePowerSum, mul_comm] using h3
  have h4' : E 4 * 4 = -(E 2 * phasePowerSum w 2) + E 1 * phasePowerSum w 3 +
      phasePowerSum w 1 * E 3 - phasePowerSum w 4 := by
    simpa [E, phasePowerSum] using h4
  have h5' : E 5 * 5 = E 2 * phasePowerSum w 3 - E 1 * phasePowerSum w 4 +
      phasePowerSum w 1 * E 4 - phasePowerSum w 2 * E 3 + phasePowerSum w 5 := by
    simpa [E, phasePowerSum] using h5
  have h6' : E 6 * 6 = -(E 2 * phasePowerSum w 4) + E 1 * phasePowerSum w 5 +
      phasePowerSum w 1 * E 5 - phasePowerSum w 2 * E 4 +
      E 3 * phasePowerSum w 3 - phasePowerSum w 6 := by
    simpa [E, phasePowerSum] using h6
  have h7' : E 7 * 7 = E 2 * phasePowerSum w 5 - E 1 * phasePowerSum w 6 +
      phasePowerSum w 1 * E 6 - phasePowerSum w 2 * E 5 -
      E 3 * phasePowerSum w 4 + phasePowerSum w 3 * E 4 + phasePowerSum w 7 := by
    simpa [E, phasePowerSum] using h7
  unfold injectiveSevenTransform distinctSevenPolynomial
  change 5040 * E 7 = _
  rw [h1'] at h2' h3' h4' h5' h6' h7'
  have e2 : E 2 = (phasePowerSum w 1 ^ 2 - phasePowerSum w 2) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simpa [pow_two, mul_comm] using h2'
  rw [e2] at h3' h4' h5' h6' h7'
  have e3 : E 3 = (phasePowerSum w 1 ^ 3 -
      3 * phasePowerSum w 1 * phasePowerSum w 2 + 2 * phasePowerSum w 3) / 6 := by
    apply (eq_div_iff (by norm_num : (6 : ℂ) ≠ 0)).2
    ring_nf at h3' ⊢
    linear_combination 2 * h3'
  rw [e3] at h4' h5' h6' h7'
  have e4 : E 4 = (phasePowerSum w 1 ^ 4 -
      6 * phasePowerSum w 1 ^ 2 * phasePowerSum w 2 + 3 * phasePowerSum w 2 ^ 2 +
      8 * phasePowerSum w 1 * phasePowerSum w 3 - 6 * phasePowerSum w 4) / 24 := by
    apply (eq_div_iff (by norm_num : (24 : ℂ) ≠ 0)).2
    ring_nf at h4' ⊢
    linear_combination 6 * h4'
  rw [e4] at h5' h6' h7'
  have e5 : E 5 = (phasePowerSum w 1 ^ 5 -
      10 * phasePowerSum w 1 ^ 3 * phasePowerSum w 2 +
      15 * phasePowerSum w 1 * phasePowerSum w 2 ^ 2 +
      20 * phasePowerSum w 1 ^ 2 * phasePowerSum w 3 -
      20 * phasePowerSum w 2 * phasePowerSum w 3 -
      30 * phasePowerSum w 1 * phasePowerSum w 4 + 24 * phasePowerSum w 5) / 120 := by
    apply (eq_div_iff (by norm_num : (120 : ℂ) ≠ 0)).2
    ring_nf at h5' ⊢
    linear_combination 24 * h5'
  rw [e5] at h6' h7'
  have e6 : E 6 = (phasePowerSum w 1 ^ 6 -
      15 * phasePowerSum w 1 ^ 4 * phasePowerSum w 2 +
      45 * phasePowerSum w 1 ^ 2 * phasePowerSum w 2 ^ 2 -
      15 * phasePowerSum w 2 ^ 3 + 40 * phasePowerSum w 1 ^ 3 * phasePowerSum w 3 -
      120 * phasePowerSum w 1 * phasePowerSum w 2 * phasePowerSum w 3 +
      40 * phasePowerSum w 3 ^ 2 - 90 * phasePowerSum w 1 ^ 2 * phasePowerSum w 4 +
      90 * phasePowerSum w 2 * phasePowerSum w 4 +
      144 * phasePowerSum w 1 * phasePowerSum w 5 - 120 * phasePowerSum w 6) / 720 := by
    apply (eq_div_iff (by norm_num : (720 : ℂ) ≠ 0)).2
    ring_nf at h6' ⊢
    linear_combination 120 * h6'
  rw [e6] at h7'
  ring_nf at h7' ⊢
  linear_combination 720 * h7'

/-! ## Leading repeated-coordinate layers -/

/-- The five-block part of the Newton correction. -/
def fiveBlockCorrection (p1 p2 p3 : ℂ) : ℂ :=
  105 * p1 ^ 3 * p2 ^ 2 + 70 * p1 ^ 4 * p3

/-- The rest of `D₇`; every displayed monomial has at most four factors. -/
def atMostFourBlockCorrection (p1 p2 p3 p4 p5 p6 p7 : ℂ) : ℂ :=
  -105 * p1 * p2 ^ 3 - 420 * p1 ^ 2 * p2 * p3 - 210 * p1 ^ 3 * p4
    + 210 * p2 ^ 2 * p3 + 280 * p1 * p3 ^ 2 + 630 * p1 * p2 * p4
    + 504 * p1 ^ 2 * p5 - 420 * p3 * p4 - 504 * p2 * p5
    - 840 * p1 * p6 + 720 * p7

/-- The repeated-coordinate integrand before summing over frequency. -/
def repeatedSevenTransform (p1 p2 p3 p4 p5 p6 p7 : ℂ) : ℂ :=
  p1 ^ 14 - distinctSevenPolynomial p1 p2 p3 p4 p5 p6 p7 ^ 2

/-- The lower-block tail after removing the `k=13` and `k=12` layers.  Writing
`D₇ = u + a + b + c`, the formula is the unremoved part of `u² - D₇²`. -/
def atMostElevenBlockRemainder (p1 p2 p3 p4 p5 p6 p7 : ℂ) : ℂ :=
  let u := p1 ^ 7
  let a := -21 * p1 ^ 5 * p2
  let b := fiveBlockCorrection p1 p2 p3
  let c := atMostFourBlockCorrection p1 p2 p3 p4 p5 p6 p7
  (-2 * u * c - 2 * a * b - 2 * a * c - b ^ 2 - 2 * b * c - c ^ 2)

/-- **Exact leading Möbius layers.**  The coefficient `42=2*C(7,2)` is the one-repeat stratum.
The next two coefficients combine the square of that correction with the two five-block cycle
types. -/
theorem repeatedSevenTransform_leading_layers (p1 p2 p3 p4 p5 p6 p7 : ℂ) :
    repeatedSevenTransform p1 p2 p3 p4 p5 p6 p7 =
      42 * p2 * p1 ^ 12 - 651 * p2 ^ 2 * p1 ^ 10 - 140 * p3 * p1 ^ 11 +
        atMostElevenBlockRemainder p1 p2 p3 p4 p5 p6 p7 := by
  simp only [repeatedSevenTransform, distinctSevenPolynomial, fiveBlockCorrection,
    atMostFourBlockCorrection, atMostElevenBlockRemainder]
  ring

/-! ## Exact coefficient and production-budget certificates -/

/-- Absolute coefficient envelope grouped by number of free blocks/factors. -/
def repeatedCoefficientEnvelope (x : ℕ) : ℕ :=
  42 * x ^ 13 + 791 * x ^ 12 + 8820 * x ^ 11 + 64743 * x ^ 10 +
    328986 * x ^ 9 + 1184153 * x ^ 8 + 3034920 * x ^ 7 +
    5482456 * x ^ 6 + 6787872 * x ^ 5 + 5450256 * x ^ 4 +
    2540160 * x ^ 3 + 518400 * x ^ 2

/-- Total absolute coefficient mass of the repeated transform. -/
theorem repeatedCoefficientEnvelope_one : repeatedCoefficientEnvelope 1 = 25401599 := by
  norm_num [repeatedCoefficientEnvelope]

/-- Even after discarding the favorable `C^(k/14-1)` powers, the production-size graded Hölder
envelope is less than `1/779` of the fourteenth-moment barrier. -/
theorem production_repeatedCoefficientEnvelope_absorbs_779 :
    779 * repeatedCoefficientEnvelope (2 ^ 15) < (2 ^ 15) ^ 14 := by
  norm_num [repeatedCoefficientEnvelope]

/-- The preceding integer is sharp at the next denominator: the same coarse certificate does not
reach `1/780`.  This is a method boundary, not a counterexample to the analytic target. -/
theorem production_repeatedCoefficientEnvelope_not_absorbs_780 :
    ¬780 * repeatedCoefficientEnvelope (2 ^ 15) < (2 ^ 15) ^ 14 := by
  norm_num [repeatedCoefficientEnvelope]

/-- A rational upper bound for `2^(1/7)`. -/
def seventhRootTwoUpper : ℚ := 5521 / 5000

/-- Exact certificate that the preceding rational lies strictly above the positive seventh root
of two. -/
theorem seventhRootTwoUpper_pow_seven : (2 : ℚ) < seventhRootTwoUpper ^ 7 := by
  norm_num [seventhRootTwoUpper]

/-- Rationalized production Hölder coefficient.  Writing every power of two as
`2^a (2^(1/7))^b` and replacing the root by `5521/5000` gives this upper envelope. -/
def productionHolderCoefficientUpper : ℚ :=
  42 * 2 * seventhRootTwoUpper ^ 5 +
    791 * seventhRootTwoUpper ^ 3 / 2 ^ 15 +
    8820 * seventhRootTwoUpper / 2 ^ 31 +
    64743 * seventhRootTwoUpper ^ 6 / 2 ^ 48 +
    328986 * seventhRootTwoUpper ^ 4 / 2 ^ 64 +
    1184153 * seventhRootTwoUpper ^ 2 / 2 ^ 80 +
    3034920 / 2 ^ 96 +
    5482456 * seventhRootTwoUpper ^ 5 / 2 ^ 113 +
    6787872 * seventhRootTwoUpper ^ 3 / 2 ^ 129 +
    5450256 * seventhRootTwoUpper / 2 ^ 145 +
    2540160 * seventhRootTwoUpper ^ 6 / 2 ^ 162 +
    518400 * seventhRootTwoUpper ^ 4 / 2 ^ 178

/-- **Exact `138` coefficient certificate.**  The true irrational Hölder coefficient is smaller
because `seventhRootTwoUpper` is a strict upper bound. -/
theorem productionHolderCoefficientUpper_lt_138 : productionHolderCoefficientUpper < 138 := by
  norm_num [productionHolderCoefficientUpper, seventhRootTwoUpper]

/-- The positive seventh root of two, the only irrational number in the exact production
normalization. -/
noncomputable def seventhRootTwo : ℝ := (2 : ℝ) ^ ((7 : ℝ)⁻¹)

theorem seventhRootTwo_pow_seven : seventhRootTwo ^ 7 = 2 := by
  exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)

/-- The rational certificate really is an upper bound for the positive seventh root. -/
theorem seventhRootTwo_lt_upper : seventhRootTwo < (5521 : ℝ) / 5000 := by
  have ht0 : (0 : ℝ) ≤ 5521 / 5000 := by norm_num
  have hr0 : 0 ≤ seventhRootTwo := Real.rpow_nonneg (by norm_num) _
  by_contra h
  have hle : (5521 : ℝ) / 5000 ≤ seventhRootTwo := le_of_not_gt h
  have hp := pow_le_pow_left₀ ht0 hle 7
  rw [seventhRootTwo_pow_seven] at hp
  norm_num at hp

/-- Exact (irrational) production coefficient after retaining every `2^18` fractional Hölder
power. -/
noncomputable def productionHolderCoefficient : ℝ :=
  42 * 2 * seventhRootTwo ^ 5 +
    791 * seventhRootTwo ^ 3 / 2 ^ 15 +
    8820 * seventhRootTwo / 2 ^ 31 +
    64743 * seventhRootTwo ^ 6 / 2 ^ 48 +
    328986 * seventhRootTwo ^ 4 / 2 ^ 64 +
    1184153 * seventhRootTwo ^ 2 / 2 ^ 80 +
    3034920 / 2 ^ 96 +
    5482456 * seventhRootTwo ^ 5 / 2 ^ 113 +
    6787872 * seventhRootTwo ^ 3 / 2 ^ 129 +
    5450256 * seventhRootTwo / 2 ^ 145 +
    2540160 * seventhRootTwo ^ 6 / 2 ^ 162 +
    518400 * seventhRootTwo ^ 4 / 2 ^ 178

/-- **Machine-checked true coefficient bound.**  This closes the numerical part of the repeated
Hölder absorption without replacing the seventh root by an unverified decimal. -/
theorem productionHolderCoefficient_lt_138 : productionHolderCoefficient < 138 := by
  have hr0 : 0 ≤ seventhRootTwo := Real.rpow_nonneg (by norm_num) _
  have hroot := seventhRootTwo_lt_upper.le
  calc
    productionHolderCoefficient ≤
        42 * 2 * ((5521 : ℝ) / 5000) ^ 5 +
          791 * ((5521 : ℝ) / 5000) ^ 3 / 2 ^ 15 +
          8820 * ((5521 : ℝ) / 5000) / 2 ^ 31 +
          64743 * ((5521 : ℝ) / 5000) ^ 6 / 2 ^ 48 +
          328986 * ((5521 : ℝ) / 5000) ^ 4 / 2 ^ 64 +
          1184153 * ((5521 : ℝ) / 5000) ^ 2 / 2 ^ 80 +
          3034920 / 2 ^ 96 +
          5482456 * ((5521 : ℝ) / 5000) ^ 5 / 2 ^ 113 +
          6787872 * ((5521 : ℝ) / 5000) ^ 3 / 2 ^ 129 +
          5450256 * ((5521 : ℝ) / 5000) / 2 ^ 145 +
          2540160 * ((5521 : ℝ) / 5000) ^ 6 / 2 ^ 162 +
          518400 * ((5521 : ℝ) / 5000) ^ 4 / 2 ^ 178 := by
      unfold productionHolderCoefficient
      gcongr
    _ < 138 := by norm_num

/-- Production repeated-coordinate population. -/
def productionRepeatedPopulation : ℕ :=
  (2 ^ 30) ^ 14 - ((2 ^ 30).descFactorial 7) ^ 2

/-- Population of the exact one-repeat strata: choose the side and pair (`42`), then use six and
seven distinct values. -/
def productionExactOneRepeatPopulation : ℕ :=
  42 * (2 ^ 30).descFactorial 6 * (2 ^ 30).descFactorial 7

/-- The uncentered repeated population is itself `1386--1387` times the entire corrected slack;
positivity cannot control this sector. -/
theorem production_repeatedPopulation_raw_gap :
    1386 *
          (productionQ * 127009 * (2 ^ 30) ^ 7) <
        productionRepeatedPopulation ∧
      productionRepeatedPopulation <
        1387 * (productionQ * 127009 * (2 ^ 30) ^ 7) := by
  norm_num [productionRepeatedPopulation, productionQ, Nat.descFactorial]

/-- Exact-one-repeat tuples account for all but less than `1/45096` of a corrected-slack unit of
the repeated population.  Analytically, however, their centered defect is the shifted odd moment
and still needs Hölder absorption. -/
theorem production_beyondOneRepeat_population_tiny :
    45096 * (productionRepeatedPopulation - productionExactOneRepeatPopulation) <
      productionQ * 127009 * (2 ^ 30) ^ 7 := by
  norm_num [productionRepeatedPopulation, productionExactOneRepeatPopulation,
    productionQ, Nat.descFactorial]

/-! ## Self-contained DC bridge and noncircular barrier -/

/-- Abstract natural-number form of the G155 repeated-sector bridge.  If the repeated wraparound
mass plus its uniform population is at most the scaled repeated energy, then wraparound is bounded
by the repeated DC defect. -/
theorem repeatedWraparound_le_dcDefect {wrap qEnergy population : ℕ}
    (h : wrap + population ≤ qEnergy) :
    wrap ≤ qEnergy - population := by
  exact Nat.le_sub_of_add_le h

/-- **Noncircular sublinear barrier.**  It is enough to control `F` at the proposed barrier and
show that every secant above it has slope strictly below one.  No a priori assumption `M ≤ T`
appears. -/
theorem sublinearBarrier {M A T B : ℝ} {F : ℝ → ℝ}
    (hrec : M ≤ A + F M) (hA : A ≤ T - B) (hFT : F T ≤ B)
    (hcontract : ∀ x, T < x → F x - F T < x - T) :
    M ≤ T := by
  by_contra hMT
  have hTM : T < M := lt_of_not_ge hMT
  have hsec := hcontract M hTM
  linarith

/-- Concrete coefficient split for the corrected depth-seven slack.  A `1/1024` secant bound is
far stronger than the strict contraction required by `sublinearBarrier`. -/
theorem productionSlackBarrier_of_slope1024 {M A S : ℝ} {F : ℝ → ℝ}
    (hrec : M ≤ A + F M)
    (hA : A ≤ 126871 * S)
    (hFT : F (127009 * S) ≤ 138 * S)
    (hslope : ∀ x, 127009 * S < x →
      F x - F (127009 * S) ≤ (x - 127009 * S) / 1024) :
    M ≤ 127009 * S := by
  apply sublinearBarrier hrec (T := 127009 * S) (B := 138 * S)
  · linarith
  · exact hFT
  · intro x hx
    have hs := hslope x hx
    have hgap : 0 < x - 127009 * S := sub_pos.mpr hx
    linarith

#print axioms injectiveSevenTransform_eq_distinctSevenPolynomial
#print axioms repeatedSevenTransform_leading_layers
#print axioms production_repeatedCoefficientEnvelope_absorbs_779
#print axioms productionHolderCoefficientUpper_lt_138
#print axioms productionHolderCoefficient_lt_138
#print axioms production_repeatedPopulation_raw_gap
#print axioms production_beyondOneRepeat_population_tiny
#print axioms repeatedWraparound_le_dcDefect
#print axioms sublinearBarrier
#print axioms productionSlackBarrier_of_slope1024

end ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
