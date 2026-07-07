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

open Finset

namespace ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

variable {m : ℕ} [NeZero m]

/-- **The local triple-convolution target.**  This is the per-frequency version of the R23
energy input, with exactly the scale predicted by the probes:
`‖J∗J∗J(d)‖ ≲ √C · m · q^(3/2)`. -/
def TripleConvPointwiseBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∀ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ C * (m : ℝ) ^ 2 * (q : ℝ) ^ 3

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

end ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget.tripleConvPointwiseBound_of_uniform_sq_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget.tripleConvEnergyBound_of_pointwise
