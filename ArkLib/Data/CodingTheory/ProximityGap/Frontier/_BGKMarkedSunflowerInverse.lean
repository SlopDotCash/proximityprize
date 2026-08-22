/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSevenSubsetOverlapDecomposition

/-!
# The exact inverse of the marked sunflower transform

Write `D_r` for the marked disjoint-petal count and `W_k` for the marked `k`-subset collision
count.  The common-core decomposition gives the triangular transform

`W_k = sum_{r <= k} D_r * choose (n - 2*r) (k-r)`.

Its ordinary generating functions satisfy

`W(z) = (1+z)^n D(z/(1+z)^2)`.

If `C(t)` is the Catalan series, so `C=1+t*C^2`, the compositional inverse is
`z=C(t)-1`, hence

`D(t) = C(t)^(-n) W(C(t)-1)`.

Lagrange inversion gives, for `j <= k`, the coefficient

`[W_j]D_k = (-1)^(k-j) * (n-2*j)/(n-2*k) * choose (n-k-j-1) (k-j)`

when `n != 2*k`; the uncancelled Lagrange form extends across `n=2*k`.  At depth seven and
after the exact vanishings `D_0=D_1=0`, this becomes

`D_7 = W_7 - (n-12) W_6 + (n-10)(n-13)/2 W_5
             - (n-8)(n-12)(n-13)/6 W_4
             + (n-6)(n-11)(n-12)(n-13)/24 W_3
             - (n-4)(n-10)(n-11)(n-12)(n-13)/120 W_2`.

The file verifies this inverse algebraically and evaluates it at `n=2^30`.  The result is an
exact signed Moebius coordinate, not a new estimate: conditional on the lower triangular rows,
the inverse identity is equivalent to the original seventh row.  Its absolute coefficient mass
is between `2^143` and `2^144`.  This is coefficient amplification, not by itself a 143-bit loss:
a normalized estimate for `W_j` can contain the compensating factor `n^{-(7-j)}`.  Any useful
application must retain that scaling or prove correlated cancellation among adjacent subset
depths; unrelated unnormalized upper bounds are quantitatively vacuous.  Issue #466.
-/

set_option autoImplicit false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKMarkedSunflowerInverse

open BGKSevenSubsetOverlapDecomposition

/-! ## The Lagrange coefficient and its depth-seven specialization -/

/-- Polynomial continuation of `choose x m` to a rational upper argument. -/
noncomputable def generalizedChoose (x : Rat) (m : Nat) : Rat :=
  (∏ i ∈ Finset.range m, (x - i)) / Nat.factorial m

/-- The uncancelled Lagrange-Buermann coefficient.  The conditional second term is absent on
the diagonal, where the derivative of `z^k` contributes exactly one. -/
noncomputable def lagrangeInverseCoefficient (n : Rat) (k j : Nat) : Rat :=
  (j : Rat) / k * generalizedChoose (2 * k - n) (k - j) -
    if j < k then
      n / k * generalizedChoose (2 * k - n - 1) (k - j - 1)
    else 0

theorem lagrange_depthSeven_two (n : Rat) :
    lagrangeInverseCoefficient n 7 2 =
      -((n - 4) * (n - 10) * (n - 11) * (n - 12) * (n - 13) / 120) := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ]
  ring

theorem lagrange_depthSeven_three (n : Rat) :
    lagrangeInverseCoefficient n 7 3 =
      (n - 6) * (n - 11) * (n - 12) * (n - 13) / 24 := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ]
  ring

theorem lagrange_depthSeven_four (n : Rat) :
    lagrangeInverseCoefficient n 7 4 =
      -((n - 8) * (n - 12) * (n - 13) / 6) := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ]
  ring

theorem lagrange_depthSeven_five (n : Rat) :
    lagrangeInverseCoefficient n 7 5 =
      (n - 10) * (n - 13) / 2 := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ]
  ring

theorem lagrange_depthSeven_six (n : Rat) :
    lagrangeInverseCoefficient n 7 6 = -(n - 12) := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ]
  ring

theorem lagrange_depthSeven_seven (n : Rat) :
    lagrangeInverseCoefficient n 7 7 = 1 := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose]

/-! ## Direct triangular verification -/

def forwardTwo (_n d₂ _d₃ _d₄ _d₅ _d₆ _d₇ : Rat) : Rat := d₂

def forwardThree (n d₂ d₃ _d₄ _d₅ _d₆ _d₇ : Rat) : Rat :=
  (n - 4) * d₂ + d₃

def forwardFour (n d₂ d₃ d₄ _d₅ _d₆ _d₇ : Rat) : Rat :=
  (n - 4) * (n - 5) / 2 * d₂ + (n - 6) * d₃ + d₄

def forwardFive (n d₂ d₃ d₄ d₅ _d₆ _d₇ : Rat) : Rat :=
  (n - 4) * (n - 5) * (n - 6) / 6 * d₂ +
    (n - 6) * (n - 7) / 2 * d₃ + (n - 8) * d₄ + d₅

def forwardSix (n d₂ d₃ d₄ d₅ d₆ _d₇ : Rat) : Rat :=
  (n - 4) * (n - 5) * (n - 6) * (n - 7) / 24 * d₂ +
    (n - 6) * (n - 7) * (n - 8) / 6 * d₃ +
      (n - 8) * (n - 9) / 2 * d₄ + (n - 10) * d₅ + d₆

def forwardSeven (n d₂ d₃ d₄ d₅ d₆ d₇ : Rat) : Rat :=
  (n - 4) * (n - 5) * (n - 6) * (n - 7) * (n - 8) / 120 * d₂ +
    (n - 6) * (n - 7) * (n - 8) * (n - 9) / 24 * d₃ +
      (n - 8) * (n - 9) * (n - 10) / 6 * d₄ +
        (n - 10) * (n - 11) / 2 * d₅ + (n - 12) * d₆ + d₇

/-- Exact depth-seven inversion of the lower-triangular common-core transform. -/
theorem forward_depthSeven_inverse (n d₂ d₃ d₄ d₅ d₆ d₇ : Rat) :
    d₇ = forwardSeven n d₂ d₃ d₄ d₅ d₆ d₇ -
      (n - 12) * forwardSix n d₂ d₃ d₄ d₅ d₆ d₇ +
      ((n - 10) * (n - 13) / 2) * forwardFive n d₂ d₃ d₄ d₅ d₆ d₇ -
      ((n - 8) * (n - 12) * (n - 13) / 6) * forwardFour n d₂ d₃ d₄ d₅ d₆ d₇ +
      ((n - 6) * (n - 11) * (n - 12) * (n - 13) / 24) *
        forwardThree n d₂ d₃ d₄ d₅ d₆ d₇ -
      ((n - 4) * (n - 10) * (n - 11) * (n - 12) * (n - 13) / 120) *
        forwardTwo n d₂ d₃ d₄ d₅ d₆ d₇ := by
  norm_num [forwardSeven, forwardSix, forwardFive, forwardFour, forwardThree, forwardTwo]
  ring

/-- Once rows two through six are fixed, the signed inverse equation is equivalent to the
original seventh triangular row.  Thus inversion alone contributes no new cancellation. -/
theorem seventh_forward_iff_inverse
    (n d₂ d₃ d₄ d₅ d₆ d₇ w₇ : Rat) :
    w₇ = forwardSeven n d₂ d₃ d₄ d₅ d₆ d₇ ↔
      d₇ = w₇ - (n - 12) * forwardSix n d₂ d₃ d₄ d₅ d₆ d₇ +
        ((n - 10) * (n - 13) / 2) * forwardFive n d₂ d₃ d₄ d₅ d₆ d₇ -
        ((n - 8) * (n - 12) * (n - 13) / 6) * forwardFour n d₂ d₃ d₄ d₅ d₆ d₇ +
        ((n - 6) * (n - 11) * (n - 12) * (n - 13) / 24) *
          forwardThree n d₂ d₃ d₄ d₅ d₆ d₇ -
        ((n - 4) * (n - 10) * (n - 11) * (n - 12) * (n - 13) / 120) *
          forwardTwo n d₂ d₃ d₄ d₅ d₆ d₇ := by
  constructor
  · intro h
    rw [h]
    exact forward_depthSeven_inverse n d₂ d₃ d₄ d₅ d₆ d₇
  · intro h
    let R : Rat :=
      -(n - 12) * forwardSix n d₂ d₃ d₄ d₅ d₆ d₇ +
        ((n - 10) * (n - 13) / 2) * forwardFive n d₂ d₃ d₄ d₅ d₆ d₇ -
        ((n - 8) * (n - 12) * (n - 13) / 6) * forwardFour n d₂ d₃ d₄ d₅ d₆ d₇ +
        ((n - 6) * (n - 11) * (n - 12) * (n - 13) / 24) *
          forwardThree n d₂ d₃ d₄ d₅ d₆ d₇ -
        ((n - 4) * (n - 10) * (n - 11) * (n - 12) * (n - 13) / 120) *
          forwardTwo n d₂ d₃ d₄ d₅ d₆ d₇
    have h' : d₇ = w₇ + R := by
      simpa only [R, sub_eq_add_neg, neg_mul, add_assoc] using h
    have hinv' : d₇ = forwardSeven n d₂ d₃ d₄ d₅ d₆ d₇ + R := by
      simpa only [R, sub_eq_add_neg, neg_mul, add_assoc] using
        forward_depthSeven_inverse n d₂ d₃ d₄ d₅ d₆ d₇
    calc
      w₇ = d₇ - R := (eq_sub_iff_add_eq).2 h'.symm
      _ = forwardSeven n d₂ d₃ d₄ d₅ d₆ d₇ := (sub_eq_iff_eq_add).2 hinv'

/-! ## Production coefficients and the absolute-value no-go -/

/-- The production subgroup cardinality, local to the inverse audit. -/
def inverseProductionN : Nat := 2 ^ 30

def productionInverseCoefficientTwo : Int :=
  -11893730218704677490033500267969392658087364

def productionInverseCoefficientThree : Int :=
  55384497657976457035751848996241837

def productionInverseCoefficientFour : Int :=
  -206323333539828500854210352

def productionInverseCoefficientFive : Int :=
  576460739955392577

def productionInverseCoefficientSix : Int := -1073741812

def productionInverseCoefficientSeven : Int := 1

theorem production_inverse_coefficients_exact :
    lagrangeInverseCoefficient inverseProductionN 7 2 =
        (productionInverseCoefficientTwo : Rat) ∧
    lagrangeInverseCoefficient inverseProductionN 7 3 =
        (productionInverseCoefficientThree : Rat) ∧
    lagrangeInverseCoefficient inverseProductionN 7 4 =
        (productionInverseCoefficientFour : Rat) ∧
    lagrangeInverseCoefficient inverseProductionN 7 5 =
        (productionInverseCoefficientFive : Rat) ∧
    lagrangeInverseCoefficient inverseProductionN 7 6 =
        (productionInverseCoefficientSix : Rat) ∧
    lagrangeInverseCoefficient inverseProductionN 7 7 =
        (productionInverseCoefficientSeven : Rat) := by
  norm_num [lagrangeInverseCoefficient, generalizedChoose, Finset.prod_range_succ,
    inverseProductionN, productionInverseCoefficientTwo, productionInverseCoefficientThree,
    productionInverseCoefficientFour, productionInverseCoefficientFive,
    productionInverseCoefficientSix, productionInverseCoefficientSeven, Nat.factorial]

/-- Total absolute coefficient mass in the production inverse. -/
def productionInverseAbsoluteMass : Nat :=
  productionInverseCoefficientTwo.natAbs + productionInverseCoefficientThree.natAbs +
    productionInverseCoefficientFour.natAbs + productionInverseCoefficientFive.natAbs +
      productionInverseCoefficientSix.natAbs + productionInverseCoefficientSeven.natAbs

theorem production_inverse_absolute_mass_exact :
    productionInverseAbsoluteMass =
      11893730274089175354333291420010483537673943 := by
  norm_num [productionInverseAbsoluteMass, productionInverseCoefficientTwo,
    productionInverseCoefficientThree, productionInverseCoefficientFour,
    productionInverseCoefficientFive, productionInverseCoefficientSix,
    productionInverseCoefficientSeven]

/-- The coefficient `l1` mass lies between 143 and 144 bits.  This theorem deliberately does not
call that a loss: comparison with a collision estimate requires the depth-dependent normalization
of every `W_j`. -/
theorem production_inverse_absolute_mass_between_pow143_pow144 :
    2 ^ 143 < productionInverseAbsoluteMass ∧ productionInverseAbsoluteMass < 2 ^ 144 := by
  norm_num [productionInverseAbsoluteMass, productionInverseCoefficientTwo,
    productionInverseCoefficientThree, productionInverseCoefficientFour,
    productionInverseCoefficientFive, productionInverseCoefficientSix,
    productionInverseCoefficientSeven]

#print axioms lagrange_depthSeven_two
#print axioms forward_depthSeven_inverse
#print axioms seventh_forward_iff_inverse
#print axioms production_inverse_coefficients_exact
#print axioms production_inverse_absolute_mass_between_pow143_pow144

end ArkLib.ProximityGap.Frontier.BGKMarkedSunflowerInverse
