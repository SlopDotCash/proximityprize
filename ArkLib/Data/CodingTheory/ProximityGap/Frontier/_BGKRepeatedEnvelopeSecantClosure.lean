/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKRepeatedNewtonFullEnumeration

/-!
# Concave secant closure for the repeated depth-seven Holder envelope

The full Newton enumeration reduces the repeated sector to a positive Holder envelope whose
monomials have exponents `k/14`, for `2 <= k <= 13`.  This file proves the remaining analytic
fact: above a positive target `T`, every such graded envelope has secant slope at most

`(13/14) * F(T)/T`.

At production, the moment variable is the Wick baseline plus the corrected defect.  The identities
`13!! + 127009 = 2^18` and `F(2^18*S) < 138*S` therefore make the secant slope strictly smaller
than `1/1024`.  The final theorem feeds this directly to
`productionSlackBarrier_of_slope1024`; the repeated tangent/bootstrap interface is closed.

Issue #466.
-/

set_option autoImplicit false

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
open ArkLib.ProximityGap.Frontier.RepeatedPartitionHolderBudgetPin

namespace ArkLib.ProximityGap.Frontier.BGKRepeatedEnvelopeSecantClosure

/-- A finite positive linear combination of real powers. -/
noncomputable def gradedHolderEnvelope {ι : Type*}
    (s : Finset ι) (coeff exponent : ι → ℝ) (M : ℝ) : ℝ :=
  ∑ i ∈ s, coeff i * M ^ exponent i

/-- Bernoulli's inequality in the secant form needed for one Holder monomial. -/
theorem rpow_sub_rpow_le_tangent
    {p T M : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0 < T) (hTM : T ≤ M) :
    M ^ p - T ^ p ≤ p * (T ^ p / T) * (M - T) := by
  let u : ℝ := (M - T) / T
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hTM) hT.le
  have hu : -1 ≤ u := le_trans (by norm_num) hu0
  have hbern := rpow_one_add_le_one_add_mul_self hu hp0 hp1
  have hTu : T * (1 + u) = M := by
    dsimp [u]
    field_simp [hT.ne']
    ring
  have hpow : (T * (1 + u)) ^ p = T ^ p * (1 + u) ^ p := by
    rw [Real.mul_rpow hT.le (by linarith)]
  have hTp : 0 ≤ T ^ p := Real.rpow_nonneg hT.le p
  have hmul := mul_le_mul_of_nonneg_left hbern hTp
  calc
    M ^ p - T ^ p = T ^ p * (1 + u) ^ p - T ^ p := by rw [← hTu, hpow]
    _ ≤ T ^ p * (1 + p * u) - T ^ p := sub_le_sub_right hmul _
    _ = p * (T ^ p / T) * (M - T) := by
      dsimp [u]
      field_simp [hT.ne']
      ring

/-- Replace the individual exponent by a common upper exponent in the tangent coefficient. -/
theorem rpow_sub_rpow_le_common_tangent
    {p a T M : ℝ} (hp0 : 0 ≤ p) (hpa : p ≤ a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hTM : T ≤ M) :
    M ^ p - T ^ p ≤ a * (T ^ p / T) * (M - T) := by
  have hone : p ≤ 1 := hpa.trans ha1
  refine (rpow_sub_rpow_le_tangent hp0 hone hT hTM).trans ?_
  have hratio : 0 ≤ T ^ p / T := div_nonneg (Real.rpow_nonneg hT.le p) hT.le
  have hgap : 0 ≤ M - T := sub_nonneg.mpr hTM
  gcongr

/-- **Graded-envelope secant theorem.**  A positive sum of powers with exponents in `[0,a]`,
where `a <= 1`, has secant slope above `T` at most `a*F(T)/T`. -/
theorem gradedHolderEnvelope_secant
    {ι : Type*} (s : Finset ι) (coeff exponent : ι → ℝ)
    {a T M : ℝ}
    (hcoeff : ∀ i ∈ s, 0 ≤ coeff i)
    (hexp0 : ∀ i ∈ s, 0 ≤ exponent i)
    (hexpa : ∀ i ∈ s, exponent i ≤ a)
    (ha1 : a ≤ 1) (hT : 0 < T) (hTM : T ≤ M) :
    gradedHolderEnvelope s coeff exponent M - gradedHolderEnvelope s coeff exponent T ≤
      a * (gradedHolderEnvelope s coeff exponent T / T) * (M - T) := by
  have hterm : ∀ i ∈ s,
      coeff i * (M ^ exponent i - T ^ exponent i) ≤
        coeff i * (a * (T ^ exponent i / T) * (M - T)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (rpow_sub_rpow_le_common_tangent (hexp0 i hi) (hexpa i hi) ha1 hT hTM)
      (hcoeff i hi)
  calc
    gradedHolderEnvelope s coeff exponent M - gradedHolderEnvelope s coeff exponent T =
        ∑ i ∈ s, coeff i * (M ^ exponent i - T ^ exponent i) := by
      unfold gradedHolderEnvelope
      calc
        (∑ i ∈ s, coeff i * M ^ exponent i) -
            ∑ i ∈ s, coeff i * T ^ exponent i =
          ∑ i ∈ s, (coeff i * M ^ exponent i - coeff i * T ^ exponent i) :=
            (Finset.sum_sub_distrib _ _).symm
        _ = ∑ i ∈ s, coeff i * (M ^ exponent i - T ^ exponent i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ ≤ ∑ i ∈ s, coeff i * (a * (T ^ exponent i / T) * (M - T)) :=
      Finset.sum_le_sum fun i hi => hterm i hi
    _ = ∑ i ∈ s, (a / T * (M - T)) * (coeff i * T ^ exponent i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (a / T * (M - T)) * ∑ i ∈ s, coeff i * T ^ exponent i := by
      rw [Finset.mul_sum]
    _ = a * (gradedHolderEnvelope s coeff exponent T / T) * (M - T) := by
      unfold gradedHolderEnvelope
      ring

/-- Positivity of a graded Holder envelope at a nonnegative argument. -/
theorem gradedHolderEnvelope_nonneg
    {ι : Type*} (s : Finset ι) (coeff exponent : ι → ℝ) {M : ℝ}
    (hcoeff : ∀ i ∈ s, 0 ≤ coeff i) (hM : 0 ≤ M) :
    0 ≤ gradedHolderEnvelope s coeff exponent M := by
  unfold gradedHolderEnvelope
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hcoeff i hi) (Real.rpow_nonneg hM (exponent i))

/-! ## Production shift and the `1/1024` secant -/

/-- **Production shifted secant.**  The moment argument is the Wick baseline `13!!*S` plus the
corrected defect `x`.  Above the target `127009*S`, the graded repeated envelope has secant slope
at most `1/1024`. -/
theorem production_shifted_gradedHolderEnvelope_secant
    {ι : Type*} (s : Finset ι) (coeff exponent : ι → ℝ)
    {S x : ℝ}
    (hcoeff : ∀ i ∈ s, 0 ≤ coeff i)
    (hexp0 : ∀ i ∈ s, 0 ≤ exponent i)
    (hexp13 : ∀ i ∈ s, exponent i ≤ (13 / 14 : ℝ))
    (hS : 0 < S) (hx : 127009 * S < x)
    (hFT : gradedHolderEnvelope s coeff exponent ((2 ^ 18 : ℝ) * S) ≤ 138 * S) :
    gradedHolderEnvelope s coeff exponent (135135 * S + x) -
        gradedHolderEnvelope s coeff exponent ((2 ^ 18 : ℝ) * S) ≤
      (x - 127009 * S) / 1024 := by
  let T : ℝ := (2 ^ 18 : ℝ) * S
  let M : ℝ := 135135 * S + x
  have hT : 0 < T := mul_pos (by norm_num) hS
  have hgap : 0 < x - 127009 * S := sub_pos.mpr hx
  have hMT : T ≤ M := by
    dsimp [T, M]
    norm_num
    linarith
  have hgapEq : M - T = x - 127009 * S := by
    dsimp [M, T]
    norm_num
    ring
  have hsec := gradedHolderEnvelope_secant s coeff exponent hcoeff hexp0 hexp13
    (by norm_num : (13 / 14 : ℝ) ≤ 1) hT hMT
  have hratio :
      gradedHolderEnvelope s coeff exponent T / T ≤ (138 : ℝ) / 2 ^ 18 := by
    apply (div_le_iff₀ hT).2
    have hFT' : gradedHolderEnvelope s coeff exponent T ≤ 138 * S := by
      simpa only [T] using hFT
    calc
      gradedHolderEnvelope s coeff exponent T ≤ 138 * S := hFT'
      _ = ((138 : ℝ) / 2 ^ 18) * T := by
        dsimp [T]
        field_simp
  have hcoef :
      (13 / 14 : ℝ) * (gradedHolderEnvelope s coeff exponent T / T) ≤
        (1 : ℝ) / 1024 := by
    calc
      (13 / 14 : ℝ) * (gradedHolderEnvelope s coeff exponent T / T) ≤
          (13 / 14 : ℝ) * ((138 : ℝ) / 2 ^ 18) := by
        exact mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ (1 : ℝ) / 1024 := by norm_num
  calc
    gradedHolderEnvelope s coeff exponent (135135 * S + x) -
        gradedHolderEnvelope s coeff exponent ((2 ^ 18 : ℝ) * S) =
      gradedHolderEnvelope s coeff exponent M - gradedHolderEnvelope s coeff exponent T := rfl
    _ ≤ (13 / 14 : ℝ) *
          (gradedHolderEnvelope s coeff exponent T / T) * (M - T) := hsec
    _ = (13 / 14 : ℝ) *
          (gradedHolderEnvelope s coeff exponent T / T) * (x - 127009 * S) := by rw [hgapEq]
    _ ≤ ((1 : ℝ) / 1024) * (x - 127009 * S) :=
      mul_le_mul_of_nonneg_right hcoef hgap.le
    _ = (x - 127009 * S) / 1024 := by ring

/-- **Closed repeated-sector bootstrap.**  An injective allocation `126871*S`, together with the
graded Holder repeated envelope and its certified target value `138*S`, forces the corrected
defect below `127009*S`.  This theorem exactly instantiates
`productionSlackBarrier_of_slope1024`. -/
theorem productionSlackBarrier_of_gradedHolderEnvelope
    {ι : Type*} (s : Finset ι) (coeff exponent : ι → ℝ)
    {total injective S : ℝ}
    (hcoeff : ∀ i ∈ s, 0 ≤ coeff i)
    (hexp0 : ∀ i ∈ s, 0 ≤ exponent i)
    (hexp13 : ∀ i ∈ s, exponent i ≤ (13 / 14 : ℝ))
    (hS : 0 < S)
    (hrec : total ≤ injective +
      gradedHolderEnvelope s coeff exponent (135135 * S + total))
    (hinjective : injective ≤ 126871 * S)
    (hFT : gradedHolderEnvelope s coeff exponent ((2 ^ 18 : ℝ) * S) ≤ 138 * S) :
    total ≤ 127009 * S := by
  let F : ℝ → ℝ := fun x => gradedHolderEnvelope s coeff exponent (135135 * S + x)
  have harg : 135135 * S + 127009 * S = (2 ^ 18 : ℝ) * S := by
    norm_num
    ring
  apply productionSlackBarrier_of_slope1024 (F := F) hrec hinjective
  · dsimp [F]
    rw [harg]
    exact hFT
  · intro x hx
    dsimp [F]
    rw [harg]
    exact production_shifted_gradedHolderEnvelope_secant s coeff exponent
      hcoeff hexp0 hexp13 hS hx hFT

/-! ## The exact twelve-stratum Newton--Holder envelope -/

/-- Exponent `k/14` for the stratum `k=j+2`, so `k` runs from `2` through `13`. -/
noncomputable def repeatedHolderExponent (j : Fin 12) : ℝ := ((j.val + 2 : ℕ) : ℝ) / 14

/-- Coefficient `B_k*N^(1-k/14)` for the stratum `k=j+2`. -/
noncomputable def repeatedHolderCoefficient (N : ℝ) (j : Fin 12) : ℝ :=
  (repeatedMobiusMass (j.val + 2) : ℝ) * N ^ (1 - repeatedHolderExponent j)

/-- **Exact repeated Holder envelope**
`F_N(M)=sum_(k=2)^13 B_k*N^(1-k/14)*M^(k/14)`. -/
noncomputable def repeatedHolderEnvelope (N M : ℝ) : ℝ :=
  gradedHolderEnvelope Finset.univ (repeatedHolderCoefficient N) repeatedHolderExponent M

/-- The exact Newton masses give nonnegative coefficients for `N >= 0`. -/
theorem repeatedHolderCoefficient_nonneg {N : ℝ} (hN : 0 ≤ N) (j : Fin 12) :
    0 ≤ repeatedHolderCoefficient N j := by
  unfold repeatedHolderCoefficient
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hN _)

/-- Every exact stratum exponent lies in `[0,13/14]`. -/
theorem repeatedHolderExponent_range (j : Fin 12) :
    0 ≤ repeatedHolderExponent j ∧ repeatedHolderExponent j ≤ (13 / 14 : ℝ) := by
  constructor
  · unfold repeatedHolderExponent
    positivity
  · unfold repeatedHolderExponent
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 14)
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    exact_mod_cast (show j.val + 2 ≤ 13 by omega)

/-- Production secant theorem for the literal twelve-stratum Newton--Holder envelope. -/
theorem production_repeatedHolderEnvelope_secant
    {N S x : ℝ} (hN : 0 ≤ N) (hS : 0 < S) (hx : 127009 * S < x)
    (hFT : repeatedHolderEnvelope N ((2 ^ 18 : ℝ) * S) ≤ 138 * S) :
    repeatedHolderEnvelope N (135135 * S + x) -
        repeatedHolderEnvelope N ((2 ^ 18 : ℝ) * S) ≤
      (x - 127009 * S) / 1024 := by
  apply production_shifted_gradedHolderEnvelope_secant Finset.univ
    (repeatedHolderCoefficient N) repeatedHolderExponent
  · intro j hj
    exact repeatedHolderCoefficient_nonneg hN j
  · intro j hj
    exact (repeatedHolderExponent_range j).1
  · intro j hj
    exact (repeatedHolderExponent_range j).2
  · exact hS
  · exact hx
  · exact hFT

/-- **Literal repeated-envelope bootstrap closure.**  This is the final consumer-facing form:
the injective `126871` allocation plus the exact twelve Newton strata force the public `127009`
target. -/
theorem productionSlackBarrier_of_repeatedHolderEnvelope
    {N total injective S : ℝ}
    (hN : 0 ≤ N) (hS : 0 < S)
    (hrec : total ≤ injective + repeatedHolderEnvelope N (135135 * S + total))
    (hinjective : injective ≤ 126871 * S)
    (hFT : repeatedHolderEnvelope N ((2 ^ 18 : ℝ) * S) ≤ 138 * S) :
    total ≤ 127009 * S := by
  apply productionSlackBarrier_of_gradedHolderEnvelope Finset.univ
    (repeatedHolderCoefficient N) repeatedHolderExponent
  · intro j hj
    exact repeatedHolderCoefficient_nonneg hN j
  · intro j hj
    exact (repeatedHolderExponent_range j).1
  · intro j hj
    exact (repeatedHolderExponent_range j).2
  · exact hS
  · exact hrec
  · exact hinjective
  · exact hFT

#print axioms rpow_sub_rpow_le_tangent
#print axioms gradedHolderEnvelope_secant
#print axioms production_shifted_gradedHolderEnvelope_secant
#print axioms productionSlackBarrier_of_gradedHolderEnvelope
#print axioms production_repeatedHolderEnvelope_secant
#print axioms productionSlackBarrier_of_repeatedHolderEnvelope

end ArkLib.ProximityGap.Frontier.BGKRepeatedEnvelopeSecantClosure
