/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic

/-!
# Exact P1 arithmetic for the rate-quarter common-factor amplifier

The maximally thickened `mu_16` construction has one hole, no triple-core
coordinates, core size `8m+r`, and `n+2` charged scalars.  A common factor
with `2d` roots can turn `2d` singleton coordinates into triple-core zeros;
turning `d` other singleton coordinates into isolated holes compensates their
dead-coordinate cost.  Every core grows by `d`, while the charged count stays
`n+2`.

The primitive direction `(X,1)` leaves room for a common factor of degree
`m-2`, so the maximal integer choice is

```text
d = (m-2)/2 = 33,554,431.
```

This file certifies the resulting threshold and radius, and the two triples
of unsafe multiplicative cosets used on the old fibre `z^15` and the new-hole
fibre `z^13`.  Scaling the affine hole row `(x,2)` by the common-factor value
does not change its three Möbius constants.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev d : ℕ := (m - 2) / 2
abbrev amplifiedCore : ℕ := 8 * m + r + d
abbrev amplifiedThreshold : ℕ := amplifiedCore + 1
abbrev radiusNumerator : ℕ := N - amplifiedThreshold

theorem two_mul_d_eq_m_sub_two : 2 * d = m - 2 := by norm_num [d, m]

theorem common_factor_degree_budget :
    3 * m + 2 * d + 1 = k - 1 ∧ 3 * m + 2 * d + 1 < k := by
  norm_num [d, m, k]

theorem amplified_core_value : amplifiedCore = 592794964 := by
  norm_num [amplifiedCore, m, r, d]

theorem amplified_threshold_value : amplifiedThreshold = 592794965 := by
  norm_num [amplifiedThreshold, amplifiedCore, m, r, d]

theorem radius_numerator_value : radiusNumerator = 480946859 := by
  norm_num [radiusNumerator, amplifiedThreshold, amplifiedCore, N, m, r, d]

/-- Exact ownership ledger of the maximal amplifier. -/
theorem maximal_amplifier_ledger :
    (2 * d) + (d + 1) + (N - 2 * d - (d + 1)) = N ∧
      (N - 2 * d - (d + 1)) + 3 * (d + 1) = N + 2 ∧
      2 * (d + 1) - 2 * d = 2 := by
  norm_num [d, m, N]

/-- Radius of the maximal common-factor amplification. -/
noncomputable abbrev delta : ℝ≥0 := radiusNumerator / N

theorem delta_eq_fortyThree_over_ninetySix_correction :
    delta = (43 / 96 : ℝ≥0) + 1 / (3 * N : ℕ) := by
  apply NNReal.coe_injective
  push_cast
  norm_num [delta, radiusNumerator, amplifiedThreshold, amplifiedCore,
    N, m, r, d]

theorem agreement_mass_eq_amplifiedThreshold :
    (1 - delta) * (N : ℝ≥0) = amplifiedThreshold := by
  have hd : delta ≤ 1 := by
    norm_num [delta, radiusNumerator, amplifiedThreshold, amplifiedCore,
      N, m, r, d]
    rw [div_le_one] <;> norm_num
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub hd]
  push_cast
  norm_num [delta, radiusNumerator, amplifiedThreshold, amplifiedCore,
    N, m, r, d]

/-! ## Kernel-cheap field certificates -/

private def binaryPowAux {M0 : Type*} [Monoid M0] (a : M0) (n : ℕ) : ℕ → M0
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then
        binaryPowAux (a * a) (n / 2) fuel
      else
        a * binaryPowAux (a * a) (n / 2) fuel

private def binaryPow {M0 : Type*} [Monoid M0] (a : M0) (n : ℕ) : M0 :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M0 : Type*} [Monoid M0]
    (a : M0) (n fuel : ℕ) (hnfuel : n < fuel) :
    binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M0 : Type*} [Monoid M0] (a : M0) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

/-- Base-factor values on the new isolated-hole fibre `z^13`. -/
def newHoleValue : Fin 3 → F := ![
  0,
  233203260543127995690583097229908235731126990090,
  101031111753530261830244986280745716342112414227]

/-- Möbius multipliers for the scaled affine row on `z^13`. -/
def newUnsafeConstant : Fin 3 → F := ![
  182687704666362864775460604089535377560070782976,
  357427157257065199771064609774836810806559371356,
  48131014922838568432685688908340148811467554291]

theorem newHoleValue_pairwise_ne : Function.Injective newHoleValue := by decide

theorem newHoleValue_ne_two (i : Fin 3) : newHoleValue i ≠ (2 : F) := by
  fin_cases i <;> decide

theorem newUnsafeConstant_formula (i : Fin 3) :
    newUnsafeConstant i = (newHoleValue i - 1) / (2 - newHoleValue i) := by
  have hden : (2 : F) - newHoleValue i ≠ 0 :=
    sub_ne_zero.mpr (newHoleValue_ne_two i).symm
  apply (eq_div_iff hden).2
  fin_cases i <;> decide

theorem newUnsafeConstant_pow_N_ne_one (i : Fin 3) :
    newUnsafeConstant i ^ N ≠ (1 : F) := by
  fin_cases i <;> rw [← binaryPow_eq_pow] <;> decide

/-- Kind `0` is the new `z^13` hole cell and kind `1` is the old residual
`z^15` hole cell. -/
def holeConstant : Fin 2 → Fin 3 → F := ![
  newUnsafeConstant,
  unsafeConstant]

def holeFibreValue : Fin 2 → F := ![z ^ 13, z ^ 15]

/-- The `m`-th power identifies the multiplicative `mu_m` coset occupied by
the unsafe labels on one hole fibre. -/
def unsafeCosetIdentifier (a : Fin 2) (i : Fin 3) : F :=
  (holeConstant a i) ^ m * holeFibreValue a

def unsafeCosetIdentifierValue : Fin 2 → Fin 3 → F := ![
  ![330877974235427374966850242433568077423179264741,
    291611200599843110820324873054813187533506530301,
    86646757027697982669620279209948936344324667345],
  ![220152157432643145337968666600599124116095526237,
    360972264931812404820732046685265240451680767927,
    80052398452504316728884798928893888838933447382]]

theorem unsafeCosetIdentifier_eq_value (a : Fin 2) (i : Fin 3) :
    unsafeCosetIdentifier a i = unsafeCosetIdentifierValue a i := by
  fin_cases a <;> fin_cases i <;>
    rw [unsafeCosetIdentifier, holeConstant, holeFibreValue,
      unsafeCosetIdentifierValue, ← binaryPow_eq_pow] <;> decide

/-- All six unsafe `mu_m` cosets are pairwise disjoint. -/
theorem unsafeCosetIdentifier_injective :
    Function.Injective (fun ai : Fin 2 × Fin 3 =>
      unsafeCosetIdentifier ai.1 ai.2) := by
  have hvalue : Function.Injective (fun ai : Fin 2 × Fin 3 =>
      unsafeCosetIdentifierValue ai.1 ai.2) := by decide
  intro a b hab
  apply hvalue
  simpa only [unsafeCosetIdentifier_eq_value] using hab

/-- Every one of the six multipliers lies outside `mu_N`, separating every
unsafe scalar from every safe scalar `-x` in the smooth domain. -/
theorem holeConstant_pow_N_ne_one (a : Fin 2) (i : Fin 3) :
    holeConstant a i ^ N ≠ (1 : F) := by
  fin_cases a
  · exact newUnsafeConstant_pow_N_ne_one i
  · exact unsafeConstant_pow_N_ne_one i

theorem holeConstant_ne_zero (a : Fin 2) (i : Fin 3) :
    holeConstant a i ≠ 0 := by
  fin_cases a <;> fin_cases i <;> decide

/-- Equality of two unsafe labels forces equality of both their quotient
fibre kind and their source line.  This packages the six-coset certificate in
the exact form needed by the saturated stack's label injection. -/
theorem holeLabel_kind_line_eq
    {a b : Fin 2} {i j : Fin 3} {x y : F}
    (hx : x ^ m = holeFibreValue a)
    (hy : y ^ m = holeFibreValue b)
    (heq : holeConstant a i * x = holeConstant b j * y) :
    (a, i) = (b, j) := by
  apply unsafeCosetIdentifier_injective
  change unsafeCosetIdentifier a i = unsafeCosetIdentifier b j
  calc
    unsafeCosetIdentifier a i = (holeConstant a i) ^ m * x ^ m := by
      simp only [unsafeCosetIdentifier, hx]
    _ = (holeConstant a i * x) ^ m := by rw [mul_pow]
    _ = (holeConstant b j * y) ^ m := by rw [heq]
    _ = (holeConstant b j) ^ m * y ^ m := by rw [mul_pow]
    _ = unsafeCosetIdentifier b j := by
      simp only [unsafeCosetIdentifier, hy]

/-- Once the hole kind and line are fixed, unsafe-label equality also forces
equality of the underlying domain coordinates. -/
theorem holeLabel_coordinate_eq
    (a : Fin 2) (i : Fin 3) {x y : F}
    (heq : holeConstant a i * x = holeConstant a i * y) : x = y := by
  exact mul_left_cancel₀ (holeConstant_ne_zero a i) heq

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorArithmetic
#print axioms maximal_amplifier_ledger
#print axioms delta_eq_fortyThree_over_ninetySix_correction
#print axioms unsafeCosetIdentifier_injective
#print axioms holeConstant_pow_N_ne_one
#print axioms holeLabel_kind_line_eq
