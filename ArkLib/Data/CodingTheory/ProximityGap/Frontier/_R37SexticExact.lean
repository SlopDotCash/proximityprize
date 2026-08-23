/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R36JacobiPowers

/-!
# LANE B2 (#466 round 37): the sextic correlations EXACT — the campaign's open object
  reduced to bounding one explicit complete character sum

Two lemmas finish the calculus:

* **`lamTransform_shift`** — shift covariance: `c_f(j+t) = c_{f·λ_t}(j)` (shifted transforms
  are transforms of twisted weights);
* **`sextic_correlation_exact`** — hence every balanced six-`J` correlation, including the
  fully-unmatched class that is the campaign's sole remaining open object, collapses:
  `∑_j (J_{j+t₁}J_{j+t₂}J_{j+t₃})·conj(J_{j+s₁}J_{j+s₂}J_j)`
  `  = m · ∑_{u∈G} ∑_w A(u·w)·conj(B(w))·λ_{t₁}(w)`
  with `A = (f₀λ_{0})⊛(f₀λ_{t₂−t₁})⊛(f₀λ_{t₃−t₁})`-type and `B = (f₀λ_{s₁})⊛(f₀λ_{s₂})⊛f₀`
  explicit twisted `⊛`-weights (`f₀` = zero-patched `χ(1−·)`).

The right side is an EXPLICIT complete character sum over a five-parameter family.  The
named top input of the campaign (`TripleConvEnergyBound`'s unmatched class) is now literally
"this sum has Deligne-scale cancellation" — a statement about points on an explicit variety,
where Katz-class equidistribution natively applies.  Nothing else remains beneath the wall.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 37, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R37SexticExact

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation
open ArkLib.ProximityGap.Frontier.R33QuadViaWeights
open ArkLib.ProximityGap.Frontier.R35TransformRingHom
open ArkLib.ProximityGap.Frontier.R36JacobiPowers

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- **Shift covariance**: `c_f(j+t) = c_{f·λ_t}(j)`. -/
theorem lamTransform_shift (hgrp : DualFamilyGroupLaw m lam) (f : F → ℂ) (t j : ZMod m) :
    lamTransform lam f (j + t) = lamTransform lam (fun z => f z * lam t z) j := by
  rw [lamTransform, lamTransform]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [show j + t = j + t from rfl, hgrp.add_eq_mul j t z]
  ring

/-- The twisted base weight `f₀·λ_t`. -/
noncomputable def twistedWeight (χ : F → ℂ) (lam : ZMod m → F → ℂ) (t : ZMod m) : F → ℂ :=
  fun z => jacobiWeight χ z * lam t z

/-- Twisted weights vanish at the origin. -/
theorem twistedWeight_zero (t : ZMod m) : twistedWeight χ lam t 0 = 0 := by
  simp [twistedWeight, jacobiWeight]

/-- The explicit triple `⊛`-weight for shifts `(0, a, b)` relative to a base shift. -/
noncomputable def tripleTwistWeight (χ : F → ℂ) (lam : ZMod m → F → ℂ)
    (a b : ZMod m) : F → ℂ :=
  mulConv (mulConv (twistedWeight χ lam 0) (twistedWeight χ lam a))
    (twistedWeight χ lam b)

/-- Shifted triple products are transforms of triple twisted `⊛`-weights:
`J_{j+t₁}·J_{j+t₂}·J_{j+t₃} = c_{W}(j + t₁)` with
`W = tripleTwistWeight (t₂−t₁) (t₃−t₁)`… stated at base shift `j` for lags `(0,a,b)`:
`J_j·J_{j+a}·J_{j+b} = c_{tripleTwistWeight a b}(j)`. -/
theorem jacobi_triple_eq_lamTransform (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (a b j : ZMod m) :
    jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a) * jacobiCoeff χ lam (j + b)
      = lamTransform lam (tripleTwistWeight χ lam a b) j := by
  have h0 : jacobiCoeff χ lam j = lamTransform lam (twistedWeight χ lam 0) j := by
    rw [jacobiCoeff_eq_lamTransform (χ := χ) hfam j]
    congr 1
    funext z
    by_cases hz : z = 0
    · simp [twistedWeight, jacobiWeight, hz]
    · simp only [twistedWeight]
      rw [hfam.triv_on_units z hz, mul_one]
  have ha : jacobiCoeff χ lam (j + a) = lamTransform lam (twistedWeight χ lam a) j := by
    rw [jacobiCoeff_eq_lamTransform (χ := χ) hfam (j + a),
      lamTransform_shift hgrp _ a j]
    rfl
  have hb : jacobiCoeff χ lam (j + b) = lamTransform lam (twistedWeight χ lam b) j := by
    rw [jacobiCoeff_eq_lamTransform (χ := χ) hfam (j + b),
      lamTransform_shift hgrp _ b j]
    rfl
  rw [h0, ha, hb]
  rw [lamTransform_mul hfam _ _ (twistedWeight_zero 0) j]
  rw [lamTransform_mul hfam _ _ (by
    -- (tw 0 ⊛ tw a) vanishes at 0
    simp only [mulConv]
    refine Finset.sum_eq_zero (fun z hz => ?_)
    rw [mul_zero]
    simp [twistedWeight, jacobiWeight]) j]
  rfl

/-- **THE SEXTIC CORRELATIONS EXACT (round-37 main theorem).**  Every balanced six-`J`
correlation collapses to `m` times an explicit `G`-fibered complete character sum of two
triple twisted `⊛`-weights — the campaign's remaining open object in its final closed form. -/
theorem sextic_correlation_exact (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (a b a' b' t : ZMod m) :
    ∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))
      = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w := by
  classical
  have hL : ∀ j : ZMod m,
      jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b)
        = lamTransform lam (tripleTwistWeight χ lam a b) (j + t) :=
    fun j => jacobi_triple_eq_lamTransform hfam hgrp a b (j + t)
  have hR : ∀ j : ZMod m,
      jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a') * jacobiCoeff χ lam (j + b')
        = lamTransform lam (tripleTwistWeight χ lam a' b') j :=
    fun j => jacobi_triple_eq_lamTransform hfam hgrp a' b' j
  calc ∑ j : ZMod m,
      (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
        * jacobiCoeff χ lam ((j + t) + b))
      * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
        * jacobiCoeff χ lam (j + b'))
      = ∑ j : ZMod m, lamTransform lam (tripleTwistWeight χ lam a b) (j + t)
          * (starRingEnd ℂ) (lamTransform lam (tripleTwistWeight χ lam a' b') j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hL j, hR j]
    _ = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w :=
        weighted_lag_correlation' hfam hgrp _ _ t

/-- **Named final sextic input.**  This is the explicit complete character sum exposed by
`sextic_correlation_exact`: uniform cancellation for the `G`-fibered correlation of two
triple twisted `⊛`-weights, for every five-lag datum. -/
def SexticCorrelationBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (B : ℝ) : Prop :=
  ∀ a b a' b' t : ZMod m,
    ‖∑ u ∈ G, ∑ w : F,
        tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖ ≤ B

/-- Monotonicity of the final sextic input in its scalar budget. -/
theorem sexticCorrelationBound_mono {B B' : ℝ}
    (hBB' : B ≤ B') (hB : SexticCorrelationBound χ lam G B) :
    SexticCorrelationBound χ lam G B' := by
  intro a b a' b' t
  exact le_trans (hB a b a' b' t) hBB'

/-- Pointwise six-`J` bound from the final sextic input.  The exact collapse loses only
the forced quotient-duality factor `m`. -/
theorem sextic_correlation_bound_of_sexticCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : SexticCorrelationBound χ lam G B)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * B := by
  rw [sextic_correlation_exact hfam hgrp a b a' b' t]
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hB a b a' b' t) (by positivity)

/-- Pointwise six-`J` bound with an enlarged scalar budget. -/
theorem sextic_correlation_bound_of_sexticCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : SexticCorrelationBound χ lam G B)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * B' :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_mono hBB' hB) a b a' b' t

/-- Aggregate all-lag six-`J` energy from the final sextic input.  This is the direct
`L²` budget for the fully-unmatched r = 3 class once the explicit complete character sum
has a uniform bound. -/
theorem sextic_correlation_energy_bound_of_sexticCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : SexticCorrelationBound χ lam G B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) := by
  classical
  have hpoint : ∀ a b a' b' t : ZMod m,
      ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖ ^ 2
        ≤ (((m : ℝ) * B) ^ 2) := by
    intro a b a' b' t
    exact pow_le_pow_left₀ (norm_nonneg _)
      (sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp hB a b a' b' t) 2
  calc ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ∑ _a : ZMod m, ∑ _b : ZMod m, ∑ _a' : ZMod m, ∑ _b' : ZMod m,
          ∑ _t : ZMod m, ((m : ℝ) * B) ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        refine Finset.sum_le_sum (fun b _ => ?_)
        refine Finset.sum_le_sum (fun a' _ => ?_)
        refine Finset.sum_le_sum (fun b' _ => ?_)
        exact Finset.sum_le_sum (fun t _ => hpoint a b a' b' t)
    _ = ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
        ring

/-- Aggregate all-lag six-`J` energy with an enlarged scalar budget. -/
theorem sextic_correlation_energy_bound_of_sexticCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : SexticCorrelationBound χ lam G B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B') ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_mono hBB' hB)

end ArkLib.ProximityGap.Frontier.R37SexticExact

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R37SexticExact.lamTransform_shift
#print axioms ArkLib.ProximityGap.Frontier.R37SexticExact.jacobi_triple_eq_lamTransform
#print axioms ArkLib.ProximityGap.Frontier.R37SexticExact.sextic_correlation_exact
#print axioms ArkLib.ProximityGap.Frontier.R37SexticExact.sexticCorrelationBound_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R37SexticExact.sextic_correlation_bound_of_sexticCorrelationBound
#print axioms
  ArkLib.ProximityGap.Frontier.R37SexticExact.sextic_correlation_bound_of_sexticCorrelationBound_le
#print axioms
  ArkLib.ProximityGap.Frontier.R37SexticExact.sextic_correlation_energy_bound_of_sexticCorrelationBound
#print axioms
  ArkLib.ProximityGap.Frontier.R37SexticExact.sextic_correlation_energy_bound_of_sexticCorrelationBound_le
