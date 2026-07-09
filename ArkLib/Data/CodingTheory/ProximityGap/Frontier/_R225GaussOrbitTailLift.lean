/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R225 Gauss orbit-tail lift)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R224OrbitTailLiftToQuotientTail
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumOrbitReduction

/-!
# R225 (#466): Gauss-period orbit stability feeds the quotient-tail lift

R224 proves the raw-to-quotient tail lift from stable raw superlevel sets.
For the actual Gauss-period spectrum those superlevels are stable: if `u ∈ G`,
then `η_G(u*b) = η_G(b)` because multiplication by `u` permutes `G`.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift

open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- A finite multiplicative subgroup is multiplicatively closed in the
`SubgroupGaussSumOrbitReduction` sense. -/
theorem mulClosed_of_finSubgroup {G : Finset F}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G) :
    MulClosed G := by
  intro a ha b hb
  exact hG.mul_mem a ha b hb

/-- The normalized-square Gauss-period superlevel sets are stable under
multiplication by members of `G`. -/
theorem normalizedSq_superlevel_stable_of_finSubgroup
    (ψ : AddChar F ℂ) {G : Finset F} {σ θ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    {u b : F} (hu : u ∈ G)
    (hθ : θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2) :
    θ ≤ ‖eta ψ G (u * b)‖ ^ 2 / σ ^ 2 := by
  have hu0 : u ≠ 0 :=
    ArkLib.ProximityGap.E2DilationDirectCount.ne_zero_of_mem_finSubgroup hG hu
  rw [eta_orbit_invariant (mulClosed_of_finSubgroup hG) hu0 hu b]
  exact hθ

/-- Gauss-period specialization of R224: the raw nonzero tail is at most
`|G|` times the quotient-orbit survivor count.  The only remaining input is
that the quotient score `qSq` dominates every raw survivor on its orbit. -/
theorem rawNonzeroTailLeCosetScale_of_gauss_orbit_score
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (Θ : Finset ℝ) (qSq : Finset F → ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈
      ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer.nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)) :
    RawNonzeroTailLeCosetScale ψ G σ (nonzeroOrbitCarrier G) qSq Θ := by
  refine rawNonzeroTailLeCosetScale_of_orbit_superlevels
    ψ G hG Θ qSq ?_ hqSq
  intro θ hθ u hu b _hb hbθ
  exact normalizedSq_superlevel_stable_of_finSubgroup ψ hG hu hbθ

end

end ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.mulClosed_of_finSubgroup
#print axioms
  ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.normalizedSq_superlevel_stable_of_finSubgroup
#print axioms
  ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift.rawNonzeroTailLeCosetScale_of_gauss_orbit_score
