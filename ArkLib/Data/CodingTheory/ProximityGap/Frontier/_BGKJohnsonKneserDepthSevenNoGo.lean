/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Johnson/Kneser association-scheme audit for the depth-seven injective residual

Let `X` be the seven-subsets of `G`, and let `f(S)=sum S`.  This file first decomposes the exact
collision census by Johnson overlap:

`#{(S,T) : f(S)=f(T)} = sum_(j=0)^7 #{(S,T) : f(S)=f(T), |S inter T|=j}`.

The `j=6` stratum is empty over every additive group with cancellation: after removing the six
common points, equality of sums identifies the two remaining points.  Thus every sum fiber is an
independent set in the ordinary Johnson graph `J(n,7)`.

The disjoint `j=0` stratum is the Kneser graph `KG(n,7)`.  Its standard spectrum is

`(-1)^i C(n-7-i,7-i), 0<=i<=7`.

For an upper quadratic-form estimate the relevant nontrivial eigenvalue is the largest positive
one `lambda_2=C(n-9,5)`.  The larger `C(n-8,6)` is only the two-sided/absolute mixing constant.
Writing `N=C(n,7)`, `d=C(n-7,7)`, total centered collision `V=J+R`, and
`J=I_disj-Nd/q`, the upper spectral estimate rearranges exactly to

`(1-beta) J <= beta R + lambda_2*N*(1-1/q)`, `beta=(d-lambda_2)/N`.

Even granting the favorable sign `R<=0`, the resulting spectral term divided by `1-beta` is
between `2^162` and `2^163` times the coefficient-126871 seven-subset target at the literal
production parameters.  Absolute/two-sided mixing misses by `190--191` bits.  Hence association-
scheme expansion alone is quantitatively far too coarse; a surviving use needs arithmetic control
of the overlap remainder or distinguished eigenspaces.  No analytic bound is claimed.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKJohnsonKneserDepthSevenNoGo

/-! ## Exact Johnson-overlap decomposition -/

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- Ordered pairs of seven-subsets with equal sum. -/
def sevenSubsetCollisionPairs (G : Finset A) : Finset (Finset A × Finset A) :=
  (G.powersetCard 7 ×ˢ G.powersetCard 7).filter fun ST =>
    (∑ x ∈ ST.1, x) = ∑ x ∈ ST.2, x

/-- Johnson overlap of a pair. -/
def overlap (ST : Finset A × Finset A) : Nat := (ST.1 ∩ ST.2).card

/-- Equal-sum collision count in overlap stratum `j`. -/
def collisionOverlapCount (G : Finset A) (j : Nat) : Nat :=
  ((sevenSubsetCollisionPairs G).filter fun ST => overlap ST = j).card

/-- **Exact eight-stratum partition of the seven-subset collision census.** -/
theorem sum_collisionOverlapCount_eq (G : Finset A) :
    ∑ j ∈ Finset.range 8, collisionOverlapCount G j =
      (sevenSubsetCollisionPairs G).card := by
  have hmaps : ∀ ST ∈ sevenSubsetCollisionPairs G, overlap ST ∈ Finset.range 8 := by
    intro ST hST
    rw [Finset.mem_range]
    have hprod := (Finset.mem_filter.mp hST).1
    have hleft := (Finset.mem_product.mp hprod).1
    have hcard : ST.1.card = 7 := (Finset.mem_powersetCard.mp hleft).2
    have hinter : (ST.1 ∩ ST.2).card ≤ ST.1.card :=
      Finset.card_le_card Finset.inter_subset_left
    unfold overlap
    omega
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := sevenSubsetCollisionPairs G) (t := Finset.range 8) (f := overlap) hmaps
  simpa [collisionOverlapCount] using hpart.symm

/-- Equal sums cannot occur at Johnson overlap six. -/
theorem not_equal_sum_of_card_seven_of_overlap_six
    {S T : Finset A} (hS : S.card = 7) (hT : T.card = 7)
    (hinter : (S ∩ T).card = 6)
    (hsum : (∑ x ∈ S, x) = ∑ x ∈ T, x) : False := by
  let I := S ∩ T
  have hIS : I ⊆ S := by exact Finset.inter_subset_left
  have hIT : I ⊆ T := by exact Finset.inter_subset_right
  have hcardI : I.card = 6 := hinter
  have hcardSdiff : (S \ I).card = 1 := by
    rw [Finset.card_sdiff]
    have hII : I ∩ S = I := Finset.inter_eq_left.mpr hIS
    rw [hII, hS, hcardI]
  have hcardTdiff : (T \ I).card = 1 := by
    rw [Finset.card_sdiff]
    have hII : I ∩ T = I := Finset.inter_eq_left.mpr hIT
    rw [hII, hT, hcardI]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcardSdiff
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcardTdiff
  have hsumS : a + ∑ x ∈ I, x = ∑ x ∈ S, x := by
    simpa [ha] using (Finset.sum_sdiff (f := fun x : A => x) hIS)
  have hsumT : b + ∑ x ∈ I, x = ∑ x ∈ T, x := by
    simpa [hb] using (Finset.sum_sdiff (f := fun x : A => x) hIT)
  have hab : a = b := by
    apply add_right_cancel
    calc
      a + ∑ x ∈ I, x = ∑ x ∈ S, x := hsumS
      _ = ∑ x ∈ T, x := hsum
      _ = b + ∑ x ∈ I, x := hsumT.symm
  have haDiff : a ∈ S \ I := by simp [ha]
  have hbDiff : b ∈ T \ I := by simp [hb]
  have haS : a ∈ S := (Finset.mem_sdiff.mp haDiff).1
  have haT : a ∈ T := by simpa [hab] using (Finset.mem_sdiff.mp hbDiff).1
  apply (Finset.mem_sdiff.mp haDiff).2
  change a ∈ S ∩ T
  exact Finset.mem_inter.mpr ⟨haS, haT⟩

/-- **Johnson local-injectivity theorem.**  The overlap-six collision stratum is empty. -/
theorem collisionOverlapCount_six (G : Finset A) : collisionOverlapCount G 6 = 0 := by
  rw [collisionOverlapCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ST hST hoverlap
  have hp := Finset.mem_filter.mp hST
  have hprod := hp.1
  have hS := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hprod).1).2
  have hT := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hprod).2).2
  exact not_equal_sum_of_card_seven_of_overlap_six hS hT hoverlap hp.2

/-! ## Abstract centered Kneser spectral algebra -/

/-- Exact rearrangement of the one-sided Kneser mixing estimate.  Here `lambda` is the largest
positive nontrivial eigenvalue, not the absolute spectral radius. -/
theorem centered_kneser_rearrangement
    {J R N d lambda q : Real}
    (hspectral : J ≤
      (d / N) * (J + R) +
        lambda * (N * (1 - 1 / q) - (J + R) / N)) :
    (1 - (d - lambda) / N) * J ≤
      ((d - lambda) / N) * R + lambda * N * (1 - 1 / q) := by
  have hid :
      (d / N) * (J + R) +
          lambda * (N * (1 - 1 / q) - (J + R) / N) =
        ((d - lambda) / N) * (J + R) + lambda * N * (1 - 1 / q) := by
    ring
  rw [hid] at hspectral
  linarith

/-- If the overlap remainder is favorably nonpositive, the generic spectral method still pays
the amplified constant term. -/
theorem centered_kneser_bound_of_nonpositive_remainder
    {J R N d lambda q : Real}
    (hbeta : 0 ≤ (d - lambda) / N)
    (hcontract : 0 < 1 - (d - lambda) / N)
    (hR : R ≤ 0)
    (hspectral : J ≤
      (d / N) * (J + R) +
        lambda * (N * (1 - 1 / q) - (J + R) / N)) :
    J ≤ (lambda * N * (1 - 1 / q)) / (1 - (d - lambda) / N) := by
  have hrearr := centered_kneser_rearrangement hspectral
  have hbetaR : ((d - lambda) / N) * R ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hbeta hR
  apply (le_div_iff₀ hcontract).2
  linarith

/-! ## Literal production spectrum and quantitative no-go -/

def productionN : Nat := 2 ^ 30

def productionQ : Nat := productionN * (2 ^ 128 + 192) + 1

/-- `C(n,7)`, written as a fixed falling product so kernel arithmetic does not unfold `Nat.choose`
at a billion-element top argument. -/
def productionSevenSubsetCount : Nat :=
  (productionN * (productionN - 1) * (productionN - 2) * (productionN - 3) *
    (productionN - 4) * (productionN - 5) * (productionN - 6)) / 5040

/-- Kneser degree `C(n-7,7)`. -/
def productionKneserDegree : Nat :=
  ((productionN - 7) * (productionN - 8) * (productionN - 9) * (productionN - 10) *
    (productionN - 11) * (productionN - 12) * (productionN - 13)) / 5040

/-- Largest positive nontrivial eigenvalue `C(n-9,5)`. -/
def productionKneserPositiveEigenvalue : Nat :=
  ((productionN - 9) * (productionN - 10) * (productionN - 11) *
    (productionN - 12) * (productionN - 13)) / 120

/-- Absolute/two-sided nontrivial spectral radius `C(n-8,6)`. -/
def productionKneserAbsoluteEigenvalue : Nat :=
  ((productionN - 8) * (productionN - 9) * (productionN - 10) *
    (productionN - 11) * (productionN - 12) * (productionN - 13)) / 720

def productionKneserEigenvalueThreeAbs : Nat :=
  ((productionN - 10) * (productionN - 11) *
    (productionN - 12) * (productionN - 13)) / 24

def productionKneserEigenvalueFour : Nat :=
  ((productionN - 11) * (productionN - 12) * (productionN - 13)) / 6

def productionKneserEigenvalueFiveAbs : Nat :=
  ((productionN - 12) * (productionN - 13)) / 2

/-- The standard `KG(n,7)` eigenvalue list at the production `n`, ordered by Johnson grade. -/
def productionKneserEigenvalue : Fin 8 -> Int :=
  ![(productionKneserDegree : Int),
    -(productionKneserAbsoluteEigenvalue : Int),
    (productionKneserPositiveEigenvalue : Int),
    -(productionKneserEigenvalueThreeAbs : Int),
    (productionKneserEigenvalueFour : Int),
    -(productionKneserEigenvalueFiveAbs : Int),
    (productionN - 13 : Int),
    -1]

/-- The grade-two eigenvalue is the largest nontrivial eigenvalue, hence the correct one-sided
upper-mixing constant. -/
theorem production_kneser_largest_nontrivial_eigenvalue
    (i : Fin 8) (hi : i ≠ 0) :
    productionKneserEigenvalue i ≤ productionKneserPositiveEigenvalue := by
  fin_cases i <;> simp at hi
  all_goals
    norm_num [productionKneserEigenvalue, productionKneserDegree,
      productionKneserAbsoluteEigenvalue, productionKneserPositiveEigenvalue,
      productionKneserEigenvalueThreeAbs, productionKneserEigenvalueFour,
      productionKneserEigenvalueFiveAbs, productionN]

/-- The grade-one negative eigenvalue controls the two-sided absolute deviation. -/
theorem production_kneser_twoSided_eigenvalue_interval
    (i : Fin 8) (hi : i ≠ 0) :
    -(productionKneserAbsoluteEigenvalue : Int) ≤ productionKneserEigenvalue i ∧
      productionKneserEigenvalue i ≤ productionKneserAbsoluteEigenvalue := by
  fin_cases i <;> simp at hi
  all_goals
    norm_num [productionKneserEigenvalue, productionKneserDegree,
      productionKneserAbsoluteEigenvalue, productionKneserPositiveEigenvalue,
      productionKneserEigenvalueThreeAbs, productionKneserEigenvalueFour,
      productionKneserEigenvalueFiveAbs, productionN]

/-- The ordinary Johnson graph `J(n,7)` eigenvalue list
`(7-i)(n-7-i)-i` at production. -/
def productionJohnsonEigenvalue : Fin 8 -> Int :=
  ![7 * ((productionN : Int) - 7),
    6 * ((productionN : Int) - 8) - 1,
    5 * ((productionN : Int) - 9) - 2,
    4 * ((productionN : Int) - 10) - 3,
    3 * ((productionN : Int) - 11) - 4,
    2 * ((productionN : Int) - 12) - 5,
    ((productionN : Int) - 13) - 6,
    -7]

/-- The least Johnson eigenvalue is exactly `-7`. -/
theorem production_johnson_least_eigenvalue (i : Fin 8) :
    (-7 : Int) ≤ productionJohnsonEigenvalue i := by
  fin_cases i <;> norm_num [productionJohnsonEigenvalue, productionN]

theorem production_johnson_grade_seven :
    productionJohnsonEigenvalue 7 = -7 := by
  rfl

/-- Hoffman/clique-coclique fiber cap `N/(n-6)=C(n,6)/7` for `J(n,7)`. -/
def productionJohnsonFiberCap : Nat :=
  (productionN * (productionN - 1) * (productionN - 2) *
    (productionN - 3) * (productionN - 4) * (productionN - 5)) / 5040

def productionJohnsonCenteredCeiling : Rat :=
  (productionSevenSubsetCount : Rat) * productionJohnsonFiberCap -
    (productionSevenSubsetCount : Rat) ^ 2 / productionQ

def productionUpperBeta : Rat :=
  ((productionKneserDegree : Rat) - productionKneserPositiveEigenvalue) /
    productionSevenSubsetCount

def productionTwoSidedBeta : Rat :=
  ((productionKneserDegree : Rat) - productionKneserAbsoluteEigenvalue) /
    productionSevenSubsetCount

/-- One-sided upper-mixing constant after the centered rearrangement. -/
def productionUpperSpectralTerm : Rat :=
  (productionKneserPositiveEigenvalue : Rat) * productionSevenSubsetCount *
      (1 - 1 / (productionQ : Rat)) /
    (1 - productionUpperBeta)

/-- Two-sided mixing version, included to distinguish the absolute eigenvalue from the sharper
one-sided positive eigenvalue. -/
def productionTwoSidedSpectralTerm : Rat :=
  (productionKneserAbsoluteEigenvalue : Rat) * productionSevenSubsetCount *
      (1 - 1 / (productionQ : Rat)) /
    (1 - productionTwoSidedBeta)

/-- Seven-subset form of the coefficient-`126871` injective target. -/
def productionSevenSubsetTarget : Rat :=
  126871 * (productionN : Rat) ^ 7 / 5040 ^ 2

theorem production_upperBeta_range :
    0 ≤ productionUpperBeta ∧ productionUpperBeta < 1 := by
  norm_num [productionUpperBeta, productionKneserDegree,
    productionKneserPositiveEigenvalue, productionSevenSubsetCount, productionN]

/-- **One-sided Kneser upper mixing misses by 162--163 bits.** -/
theorem production_upperSpectralTerm_gap :
    2 ^ 162 * productionSevenSubsetTarget < productionUpperSpectralTerm ∧
      productionUpperSpectralTerm < 2 ^ 163 * productionSevenSubsetTarget := by
  norm_num [productionSevenSubsetTarget, productionUpperSpectralTerm, productionUpperBeta,
    productionKneserPositiveEigenvalue, productionKneserDegree, productionSevenSubsetCount,
    productionQ, productionN]

/-- The exact Johnson Hoffman cap is itself `163--164` bits too weak for the centered target. -/
theorem production_johnsonCenteredCeiling_gap :
    2 ^ 163 * productionSevenSubsetTarget < productionJohnsonCenteredCeiling ∧
      productionJohnsonCenteredCeiling < 2 ^ 164 * productionSevenSubsetTarget := by
  norm_num [productionSevenSubsetTarget, productionJohnsonCenteredCeiling,
    productionJohnsonFiberCap, productionSevenSubsetCount, productionQ, productionN]

/-- **Two-sided/absolute Kneser mixing misses by 190--191 bits.** -/
theorem production_twoSidedSpectralTerm_gap :
    2 ^ 190 * productionSevenSubsetTarget < productionTwoSidedSpectralTerm ∧
      productionTwoSidedSpectralTerm < 2 ^ 191 * productionSevenSubsetTarget := by
  norm_num [productionSevenSubsetTarget, productionTwoSidedSpectralTerm, productionTwoSidedBeta,
    productionKneserAbsoluteEigenvalue, productionKneserDegree, productionSevenSubsetCount,
    productionQ, productionN]

#print axioms sum_collisionOverlapCount_eq
#print axioms not_equal_sum_of_card_seven_of_overlap_six
#print axioms collisionOverlapCount_six
#print axioms centered_kneser_rearrangement
#print axioms centered_kneser_bound_of_nonpositive_remainder
#print axioms production_kneser_largest_nontrivial_eigenvalue
#print axioms production_kneser_twoSided_eigenvalue_interval
#print axioms production_johnson_least_eigenvalue
#print axioms production_upperBeta_range
#print axioms production_upperSpectralTerm_gap
#print axioms production_johnsonCenteredCeiling_gap
#print axioms production_twoSidedSpectralTerm_gap

end ArkLib.ProximityGap.Frontier.BGKJohnsonKneserDepthSevenNoGo
