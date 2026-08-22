/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R227 natural quotient envelope endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R226GaussQuotientTailPrizeEndpoint

/-!
# R227 (#466): natural quotient envelope to prize

R226 still asks for an explicit scaled-envelope inequality.  This file proves
that inequality for the natural quotient-orbit tail envelope

```text
(3/5) * (#(b ≠ 0) / |G|) * exp(-θ/2) + 2.
```

Multiplying by `|G|` gives exactly the corrected raw-frequency envelope
`(3/5) * #(b ≠ 0) * exp(-θ/2) + 2 * |G|`.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.Frontier.R226GaussQuotientTailPrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The natural quotient-orbit half-rate bulk-plus-two envelope. -/
def NaturalQuotientEnvelope (G : Finset F) : ℝ → ℝ :=
  fun θ => (3 / 5 : ℝ) *
    (((nonzeroFreqs (F := F)).card : ℝ) / (G.card : ℝ)) *
      Real.exp (-(θ / 2)) + 2

/-- The natural quotient envelope scales to the corrected raw envelope. -/
theorem naturalQuotientEnvelope_scale_le_raw
    (G : Finset F)
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (θ : ℝ) :
    (G.card : ℝ) * NaturalQuotientEnvelope (F := F) G θ ≤
      (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + 2 * (G.card : ℝ) := by
  have hGposNat : 0 < G.card :=
    Finset.card_pos.mpr ⟨1, hG.one_mem⟩
  have hGne : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast hGposNat.ne'
  unfold NaturalQuotientEnvelope
  apply le_of_eq
  field_simp [hGne]

/-- Prize endpoint with the natural quotient-orbit envelope.  The only tail
input is now the quotient grid-tail bound for `NaturalQuotientEnvelope`. -/
theorem prize_sq_of_gauss_natural_quotient_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTail :
      QuotientNormalizedSqGridTail (nonzeroOrbitCarrier (F := F) G) qSq Θ
        (NaturalQuotientEnvelope (F := F) G))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (depth : ℕ) {Mmax n Qfield : ℝ} {r : ℕ}
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQfield : 0 < Qfield)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Qfield ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Qfield * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_gauss_quotient_threeFifths_plus_two_tail
    ψ G hG hζ hdisj hσ qSq Θ δ (NaturalQuotientEnvelope (F := F) G)
    hqSq hQTail
    (fun θ _hθ => naturalQuotientEnvelope_scale_le_raw G hG θ)
    hδ hstair hweighted depth hcard hMmax hn hQfield hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint.naturalQuotientEnvelope_scale_le_raw
#print axioms
  ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint.prize_sq_of_gauss_natural_quotient_tail
