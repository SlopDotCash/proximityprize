/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput

/-!
# LANE B2 (#466 round 26): pointwise triple-convolution target ⇒ the R23 energy input

Round 23 isolated the remaining `r = 3` input as

  `∑ d, ‖tripleConv J d‖² ≤ C · m³ · q³`.

This brick records the sharper local target that would discharge it immediately:

  `∀ d, ‖tripleConv J d‖² ≤ C · m² · q³`.

Since there are exactly `m` frequencies in `ZMod m`, the pointwise target sums to the calibrated
energy bound.  This is deliberately small but useful: it turns the remaining analytic problem into
a uniform bound for one explicit oscillatory convolution coefficient, the natural landing zone for
Katz-style vertical equidistribution of the Jacobi angle family.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 26, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

variable {m : ℕ} [NeZero m]

/-- The explicit punctured additive triple sum behind `tripleConv`: all three entries are
nonzero and add to `d`. -/
noncomputable def additiveTripleSum (J : ZMod m → ℂ) (d : ZMod m) : ℂ :=
  ∑ y ∈ Finset.univ \ {(0 : ZMod m)},
    ∑ x ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x => d - y - x ≠ 0),
      J x * J (d - y - x) * J y

/-- The R22 punctured triple convolution is exactly the explicit nonzero additive
three-variable sum. -/
theorem tripleConv_eq_additiveTripleSum (J : ZMod m → ℂ) (d : ZMod m) :
    tripleConv J d = additiveTripleSum J d := by
  classical
  unfold tripleConv additiveTripleSum selfConv
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [Finset.sum_mul]

/-- Hermitian square expansion of the explicit additive triple sum.  This is the exact
six-variable object whose cancellation would prove the pointwise triple-convolution target. -/
theorem additiveTripleSum_norm_sq_expansion (J : ZMod m → ℂ) (d : ZMod m) :
    ((‖additiveTripleSum J d‖ ^ 2 : ℝ) : ℂ)
      = ∑ y ∈ Finset.univ \ {(0 : ZMod m)},
          ∑ x ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x => d - y - x ≠ 0),
            ∑ y' ∈ Finset.univ \ {(0 : ZMod m)},
              ∑ x' ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x' => d - y' - x' ≠ 0),
                (J x * J (d - y - x) * J y)
                  * (starRingEnd ℂ) (J x' * J (d - y' - x') * J y') := by
  classical
  have hprod :
      additiveTripleSum J d * (starRingEnd ℂ) (additiveTripleSum J d)
        = ∑ y ∈ Finset.univ \ {(0 : ZMod m)},
            ∑ x ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x => d - y - x ≠ 0),
              ∑ y' ∈ Finset.univ \ {(0 : ZMod m)},
                ∑ x' ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x' => d - y' - x' ≠ 0),
                  (J x * J (d - y - x) * J y)
                    * (starRingEnd ℂ) (J x' * J (d - y' - x') * J y') := by
    unfold additiveTripleSum
    simp_rw [map_sum]
    simp_rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_comm]
  calc ((‖additiveTripleSum J d‖ ^ 2 : ℝ) : ℂ)
      = additiveTripleSum J d * (starRingEnd ℂ) (additiveTripleSum J d) := by
        rw [RCLike.mul_conj]
        norm_cast
    _ = _ := hprod

/-- The real part of the Hermitian six-variable expansion for one additive triple coefficient. -/
noncomputable def additiveTripleHermitianExpansion (J : ZMod m → ℂ) (d : ZMod m) : ℝ :=
  (∑ y ∈ Finset.univ \ {(0 : ZMod m)},
      ∑ x ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x => d - y - x ≠ 0),
        ∑ y' ∈ Finset.univ \ {(0 : ZMod m)},
          ∑ x' ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x' => d - y' - x' ≠ 0),
            (J x * J (d - y - x) * J y)
              * (starRingEnd ℂ) (J x' * J (d - y' - x') * J y')).re

/-- The real Hermitian expansion is exactly the norm square of the additive triple sum. -/
theorem additiveTripleHermitianExpansion_eq_norm_sq (J : ZMod m → ℂ) (d : ZMod m) :
    additiveTripleHermitianExpansion J d = ‖additiveTripleSum J d‖ ^ 2 := by
  unfold additiveTripleHermitianExpansion
  have h := congrArg Complex.re (additiveTripleSum_norm_sq_expansion J d)
  rw [← h]
  exact Complex.ofReal_re _

/-- Pointwise control of the expanded six-variable Hermitian form. -/
def AdditiveTripleHermitianPointwiseBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∀ d : ZMod m, additiveTripleHermitianExpansion J d ≤ C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3

/-- Pointwise control of the explicit additive triple sum. -/
def AdditiveTriplePointwiseBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∀ d : ZMod m, ‖additiveTripleSum J d‖ ^ 2 ≤ C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3

/-- **The local triple-convolution target.**  This is the per-frequency version of the R23
energy input, with exactly the scale predicted by the probes:
`‖J∗J∗J(d)‖ ≲ √C · m · q^(3/2)`. -/
def TripleConvPointwiseBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∀ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3

/-- The expanded Hermitian target is exactly strong enough for the additive-triple pointwise
target. -/
theorem additiveTriplePointwiseBound_of_hermitianPointwiseBound
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : AdditiveTripleHermitianPointwiseBound J q C) :
    AdditiveTriplePointwiseBound J q C := by
  intro d
  rw [← additiveTripleHermitianExpansion_eq_norm_sq J d]
  exact h d

/-- The explicit additive-triple target is exactly strong enough for the existing pointwise
triple-convolution target. -/
theorem tripleConvPointwiseBound_of_additiveTriplePointwiseBound
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : AdditiveTriplePointwiseBound J q C) :
    TripleConvPointwiseBound J q C := by
  intro d
  rw [tripleConv_eq_additiveTripleSum J d]
  exact h d

/-- The triangle-inequality baseline also has a pointwise form: if `‖J_j‖² ≤ q`, then
`TripleConvPointwiseBound` holds with constant `m²`.  The prize-scale target is exactly to
replace this formal `m²` by an absolute constant. -/
theorem tripleConvPointwiseBound_of_uniform_sq_bound (J : ZMod m → ℂ) (q : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) :
    TripleConvPointwiseBound J q ((m : ℝ) ^ 2) := by
  intro d
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ j : ZMod m, ‖J j‖ ≤ Real.sqrt (q : ℝ) := by
    intro j
    have h := Real.sqrt_le_sqrt (hJ j)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hnorm := norm_tripleConv_le_card_sq_mul_bound J hB0 hJroot d
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 6 = (q : ℝ) ^ 3 := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ 6
        = ((Real.sqrt (q : ℝ)) ^ 2) ^ 3 := by ring
      _ = (q : ℝ) ^ 3 := by rw [hs2]
  calc ‖tripleConv J d‖ ^ 2
      ≤ ((m : ℝ) ^ 2 * (Real.sqrt (q : ℝ)) ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (m : ℝ) ^ 4 * (q : ℝ) ^ 3 := by
        rw [← hsqrt]
        ring
    _ = (m : ℝ) ^ 2 * (m : ℝ) ^ 2 * (q : ℝ) ^ 3 := by ring

/-- **Pointwise target ⇒ R23 named input.**  Summing the local bound over the `m` frequencies
gives `TripleConvEnergyBound` with the same constant. -/
theorem tripleConvEnergyBound_of_pointwise (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (hpt : TripleConvPointwiseBound J q C) :
    TripleConvEnergyBound J q C := by
  unfold TripleConvEnergyBound TripleConvPointwiseBound at *
  calc
    ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
        ≤ ∑ _d : ZMod m, C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3 := by
          exact Finset.sum_le_sum (fun d _ => hpt d)
    _ = (Fintype.card (ZMod m) : ℝ) * (C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
    _ = (m : ℝ) * (C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3) := by
          rw [ZMod.card]
    _ = C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

/-- The explicit additive-triple pointwise target directly discharges the R23
triple-convolution energy input. -/
theorem tripleConvEnergyBound_of_additiveTriplePointwiseBound
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : AdditiveTriplePointwiseBound J q C) :
    TripleConvEnergyBound J q C :=
  tripleConvEnergyBound_of_pointwise J q
    (tripleConvPointwiseBound_of_additiveTriplePointwiseBound J q h)

/-- The expanded Hermitian six-variable target directly discharges the R23
triple-convolution energy input. -/
theorem tripleConvEnergyBound_of_additiveTripleHermitianPointwiseBound
    (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (h : AdditiveTripleHermitianPointwiseBound J q C) :
    TripleConvEnergyBound J q C :=
  tripleConvEnergyBound_of_additiveTriplePointwiseBound J q
    (additiveTriplePointwiseBound_of_hermitianPointwiseBound J q h)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The Jacobi-specialized six-variable Hermitian target.  This is the current concrete
pointwise cancellation statement for the R23 sextic input. -/
def JacobiAdditiveTripleHermitianPointwiseBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (C : ℝ) : Prop :=
  AdditiveTripleHermitianPointwiseBound
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) (Fintype.card F) C

/-- The fully expanded Jacobi Hermitian six-variable expression at additive frequency `d`.
This is just `additiveTripleHermitianExpansion` with `J_i = jacobiCoeff χ lam i`, but spelling it
out makes the current analytic target visible without unfolding generic plumbing. -/
noncomputable def jacobiAdditiveTripleHermitianExpansion
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (d : ZMod m) : ℝ :=
  (∑ y ∈ Finset.univ \ {(0 : ZMod m)},
      ∑ x ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x => d - y - x ≠ 0),
        ∑ y' ∈ Finset.univ \ {(0 : ZMod m)},
          ∑ x' ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun x' => d - y' - x' ≠ 0),
            (R19JacobiFourierExpansion.jacobiCoeff χ lam x
              * R19JacobiFourierExpansion.jacobiCoeff χ lam (d - y - x)
              * R19JacobiFourierExpansion.jacobiCoeff χ lam y)
              * (starRingEnd ℂ)
                (R19JacobiFourierExpansion.jacobiCoeff χ lam x'
                  * R19JacobiFourierExpansion.jacobiCoeff χ lam (d - y' - x')
                  * R19JacobiFourierExpansion.jacobiCoeff χ lam y')).re

/-- The expanded Jacobi expression is the generic Hermitian expansion specialized to Jacobi
coefficients. -/
theorem jacobiAdditiveTripleHermitianExpansion_eq
    (d : ZMod m) :
    jacobiAdditiveTripleHermitianExpansion χ lam d
      = additiveTripleHermitianExpansion
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) d := by
  rfl

/-- The expanded Jacobi Hermitian expression is exactly the squared norm of the explicit
additive triple sum of Jacobi coefficients. -/
theorem jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_additiveTriple
    (d : ZMod m) :
    jacobiAdditiveTripleHermitianExpansion χ lam d
      = ‖additiveTripleSum
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) d‖ ^ 2 := by
  rw [jacobiAdditiveTripleHermitianExpansion_eq (χ := χ) (lam := lam) d,
    additiveTripleHermitianExpansion_eq_norm_sq]

/-- The expanded Jacobi Hermitian expression is exactly the squared norm of the R22
triple-convolution coefficient. -/
theorem jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv
    (d : ZMod m) :
    jacobiAdditiveTripleHermitianExpansion χ lam d
      = ‖tripleConv
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) d‖ ^ 2 := by
  rw [jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_additiveTriple (χ := χ) (lam := lam) d]
  rw [tripleConv_eq_additiveTripleSum]

/-- Fully expanded pointwise Jacobi Hermitian target. -/
def JacobiAdditiveTripleHermitianExpandedPointwiseBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (C : ℝ) : Prop :=
  ∀ d : ZMod m,
    jacobiAdditiveTripleHermitianExpansion χ lam d
      ≤ C * (m : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 3

/-- Energy-level expanded Jacobi Hermitian target.  Unlike the pointwise version, this is
exactly the R23 triple-convolution energy input after termwise identification. -/
def JacobiAdditiveTripleHermitianExpandedEnergyBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, jacobiAdditiveTripleHermitianExpansion χ lam d
    ≤ C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3

/-- The expanded Jacobi Hermitian energy target is exactly the R23 `TripleConvEnergyBound`. -/
theorem jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound {C : ℝ} :
    JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C
      ↔ TripleConvEnergyBound
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
        (Fintype.card F) C := by
  constructor
  · intro h
    unfold JacobiAdditiveTripleHermitianExpandedEnergyBound at h
    unfold TripleConvEnergyBound
    rw [← Finset.sum_congr rfl (fun d _ =>
      jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv (χ := χ) (lam := lam) d)]
    exact h
  · intro h
    unfold JacobiAdditiveTripleHermitianExpandedEnergyBound
    unfold TripleConvEnergyBound at h
    rw [Finset.sum_congr rfl (fun d _ =>
      jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv (χ := χ) (lam := lam) d)]
    exact h

/-- **Named current B-side input.**  This is the fully expanded Jacobi Hermitian pointwise
bound at the exact scale needed for the R23 triple-convolution energy. -/
def JacobiHermitianSixInput (χ : F → ℂ) (lam : ZMod m → F → ℂ) (C : ℝ) : Prop :=
  JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C

/-- The named six-variable input is exactly the pointwise R26 triple-convolution target for
Jacobi coefficients. -/
theorem jacobiHermitianSixInput_iff_tripleConvPointwiseBound {C : ℝ} :
    JacobiHermitianSixInput χ lam C
      ↔ TripleConvPointwiseBound
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
        (Fintype.card F) C := by
  constructor
  · intro h d
    rw [← jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv
      (χ := χ) (lam := lam) d]
    exact h d
  · intro h d
    rw [jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv
      (χ := χ) (lam := lam) d]
    exact h d

/-- Monotonicity of the fully expanded Jacobi Hermitian target in its scalar budget. -/
theorem jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C' := by
  intro d
  have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
  have hq : 0 ≤ (Fintype.card F : ℝ) ^ 3 := by positivity
  have hC_m : C * (m : ℝ) ^ 2 ≤ C' * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hCC' hm
  exact (h d).trans (mul_le_mul_of_nonneg_right hC_m hq)

/-- Monotonicity of the named current B-side input. -/
theorem jacobiHermitianSixInput_mono
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiHermitianSixInput χ lam C) :
    JacobiHermitianSixInput χ lam C' :=
  jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono hCC' h

/-- Monotonicity of the energy-level fully expanded Jacobi Hermitian target in its scalar
budget. -/
theorem jacobiAdditiveTripleHermitianExpandedEnergyBound_mono
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C' := by
  have hm : 0 ≤ (m : ℝ) ^ 3 := by positivity
  have hq : 0 ≤ (Fintype.card F : ℝ) ^ 3 := by positivity
  have hC_m : C * (m : ℝ) ^ 3 ≤ C' * (m : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hCC' hm
  exact h.trans (mul_le_mul_of_nonneg_right hC_m hq)

/-- A pointwise expanded Jacobi Hermitian bound sums to the corresponding energy-level
expanded bound with the same scalar budget. -/
theorem jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C := by
  unfold JacobiAdditiveTripleHermitianExpandedEnergyBound
  unfold JacobiAdditiveTripleHermitianExpandedPointwiseBound at h
  calc
    ∑ d : ZMod m, jacobiAdditiveTripleHermitianExpansion χ lam d
        ≤ ∑ _d : ZMod m, C * (m : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 3 := by
          exact Finset.sum_le_sum (fun d _ => h d)
    _ = (m : ℝ) * (C * (m : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [ZMod.card]
    _ = C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3 := by ring

/-- A pointwise expanded Jacobi Hermitian bound also supplies any enlarged energy-level
expanded budget. -/
theorem jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise_le
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C' :=
  jacobiAdditiveTripleHermitianExpandedEnergyBound_mono hCC'
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise h)

/-- The fully expanded Jacobi target is the same as the generic Jacobi Hermitian target. -/
theorem jacobiAdditiveTripleHermitianPointwiseBound_of_expanded
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    JacobiAdditiveTripleHermitianPointwiseBound χ lam C := by
  intro d
  rw [← jacobiAdditiveTripleHermitianExpansion_eq (χ := χ) (lam := lam) d]
  exact h d

/-- The Jacobi-specialized Hermitian target directly supplies the R23 `TripleConvEnergyBound`
for the Jacobi coefficient sequence. -/
theorem tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianPointwiseBound
    {C : ℝ} (h : JacobiAdditiveTripleHermitianPointwiseBound χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C :=
  tripleConvEnergyBound_of_additiveTripleHermitianPointwiseBound
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
    (Fintype.card F) h

/-- The fully expanded Jacobi Hermitian target directly supplies the R23
`TripleConvEnergyBound`. -/
theorem tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C :=
  tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianPointwiseBound
    (jacobiAdditiveTripleHermitianPointwiseBound_of_expanded h)

/-- Fully expanded Jacobi Hermitian target with an enlarged R23 budget. -/
theorem tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C' :=
  tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
    (jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono hCC' h)

/-- The named current B-side input supplies the R23 triple-convolution energy bound. -/
theorem tripleConvEnergyBound_of_jacobiHermitianSixInput
    {C : ℝ} (h : JacobiHermitianSixInput χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C :=
  tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound h

/-- The named current B-side input supplies R23 with an enlarged budget. -/
theorem tripleConvEnergyBound_of_jacobiHermitianSixInput_le
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiHermitianSixInput χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C' :=
  tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le hCC' h

/-- The energy-level expanded Jacobi Hermitian target supplies R23 exactly. -/
theorem tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C :=
  (jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
    (χ := χ) (lam := lam)).mp h

/-- Energy-level expanded Jacobi Hermitian target with an enlarged R23 budget. -/
theorem tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    TripleConvEnergyBound
      (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
      (Fintype.card F) C' :=
  tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_mono hCC' h)

/-- Jacobi Hermitian target ⇒ sextic pure-face moment bound, via R22/R23's exact collapse. -/
theorem sextic_moment_of_jacobiAdditiveTripleHermitianPointwiseBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianPointwiseBound χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianPointwiseBound h)

/-- Jacobi Hermitian target ⇒ pointwise sixth-power pure-face bound for every nonzero `s`. -/
theorem sup_pureFace_of_jacobiAdditiveTripleHermitianPointwiseBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianPointwiseBound χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianPointwiseBound h) hs

/-- Fully expanded Jacobi Hermitian target ⇒ sextic pure-face moment bound. -/
theorem sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_jacobiAdditiveTripleHermitianPointwiseBound hfam hgrp
    (jacobiAdditiveTripleHermitianPointwiseBound_of_expanded h)

/-- Fully expanded Jacobi Hermitian target ⇒ sextic pure-face moment bound with an enlarged
budget. -/
theorem sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound hfam hgrp
    (jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono hCC' h)

/-- Named B-side input ⇒ sextic pure-face moment bound. -/
theorem sextic_moment_of_jacobiHermitianSixInput
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiHermitianSixInput χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound hfam hgrp h

/-- Named B-side input ⇒ sextic pure-face moment bound with an enlarged budget. -/
theorem sextic_moment_of_jacobiHermitianSixInput_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiHermitianSixInput χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
    hfam hgrp hCC' h

/-- Energy-level expanded Jacobi Hermitian target ⇒ sextic pure-face moment bound. -/
theorem sextic_moment_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound h)

/-- Energy-level expanded Jacobi Hermitian target ⇒ sextic pure-face moment bound with an
enlarged budget. -/
theorem sextic_moment_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖R21QuarticConvolutionCollapse.pureFace
          (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sextic_moment_of_jacobiAdditiveTripleHermitianExpandedEnergyBound hfam hgrp
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_mono hCC' h)

/-- Fully expanded Jacobi Hermitian target ⇒ pointwise sixth-power pure-face bound. -/
theorem sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_jacobiAdditiveTripleHermitianPointwiseBound hfam hgrp
    (jacobiAdditiveTripleHermitianPointwiseBound_of_expanded h) hs

/-- Fully expanded Jacobi Hermitian target ⇒ pointwise sixth-power pure-face bound with an
enlarged budget. -/
theorem sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound hfam hgrp
    (jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono hCC' h) hs

/-- Named B-side input ⇒ pointwise sixth-power pure-face bound. -/
theorem sup_pureFace_of_jacobiHermitianSixInput
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiHermitianSixInput χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound hfam hgrp h hs

/-- Named B-side input ⇒ pointwise sixth-power pure-face bound with an enlarged budget. -/
theorem sup_pureFace_of_jacobiHermitianSixInput_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiHermitianSixInput χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
    hfam hgrp hCC' h hs

/-- Energy-level expanded Jacobi Hermitian target ⇒ pointwise sixth-power pure-face bound. -/
theorem sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C : ℝ} (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound h) hs

/-- Energy-level expanded Jacobi Hermitian target ⇒ pointwise sixth-power pure-face bound
with an enlarged budget. -/
theorem sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
    (hfam : R19JacobiFourierExpansion.SubgroupDualFamily G m lam)
    (hgrp : R20JacobiParseval.DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC' : C ≤ C')
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam C)
    {s : F} (hs : s ≠ 0) :
    ‖R21QuarticConvolutionCollapse.pureFace
        (fun i : ZMod m => R19JacobiFourierExpansion.jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) :=
  sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedEnergyBound hfam hgrp
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_mono hCC' h) hs

end ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget.tripleConv_eq_additiveTripleSum
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms additiveTripleSum_norm_sq_expansion
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms additiveTripleHermitianExpansion_eq_norm_sq
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms additiveTriplePointwiseBound_of_hermitianPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvPointwiseBound_of_additiveTriplePointwiseBound
#print axioms
  ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget.tripleConvPointwiseBound_of_uniform_sq_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget.tripleConvEnergyBound_of_pointwise
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_additiveTriplePointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_additiveTripleHermitianPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpansion_eq
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_additiveTriple
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpansion_eq_norm_sq_tripleConv
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiHermitianSixInput_iff_tripleConvPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianPointwiseBound_of_expanded
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpandedPointwiseBound_mono
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiHermitianSixInput_mono
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpandedEnergyBound_mono
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiHermitianSixInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiHermitianSixInput_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms tripleConvEnergyBound_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiAdditiveTripleHermitianPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiAdditiveTripleHermitianPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiHermitianSixInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiHermitianSixInput_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sextic_moment_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedPointwiseBound_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiHermitianSixInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiHermitianSixInput_le
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedEnergyBound
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget in
#print axioms sup_pureFace_of_jacobiAdditiveTripleHermitianExpandedEnergyBound_le
