/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R235 quotient residual-tail lift)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R225GaussOrbitTailLift
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R234RankSumResidualMGFConsumer

/-!
# R235 (#466): quotient residual-tail lift for the R234 split

R234 gives the raw nonzero-frequency consumer:

```text
direct raw top payment + raw residual survival tail -> quarter-MGF residual.
```

The probes, however, work on quotient/coset spectra.  This file packages the
missing deterministic lift for the residual tail: after deleting a marked raw
top set `T`, it is enough to bound the quotient residual carrier, provided raw
survivors map into quotient survivors with multiplicity at most `|G|`.

No analytic residual is proved here.  The new hypothesis
`RawResidualTailLeCosetScale` is the exact quotient-to-raw bridge that the next
arithmetic/top-rank theorem should discharge for a concrete choice of `T`.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

namespace ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift
open ArkLib.ProximityGap.Frontier.R234RankSumResidualMGFConsumer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Natural quotient carrier after deleting the marked raw top set. -/
def residualOrbitCarrier (G T : Finset F) : Finset (Finset F) :=
  (residualNonzeroFreqs (F := F) T).image
    (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)

/-- Residual quotient survival-count ceiling after deleting whatever raw top
set has been paid directly.  The quotient deletion rule is left abstract:
`Qres` is the quotient carrier that remains after the top ranks are removed. -/
def QuotientResidualGridTail {ι : Type*} (Qres : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) (Bq : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Θ, (((Qres.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ)

/-- Raw residual survivors are covered by quotient residual survivors, with
coset multiplicity at most `|G|`.  This is the residual analogue of the orbit
tail lift used in R224/R225. -/
def RawResidualTailLeCosetScale
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    {ι : Type*} (T : Finset F) (Qres : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((((residualNonzeroFreqs (F := F) T).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Qres.filter (fun i => θ ≤ qSq i)).card : ℝ))

/-- Natural residual orbit lift for Gauss-period scores.  If deleting `T`
leaves a residual raw carrier stable under multiplication by `G`, then the
residual superlevel count is at most `|G|` times the corresponding residual
orbit count. -/
theorem rawResidualTailLeCosetScale_of_gauss_residual_orbit_score
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ} (T : Finset F)
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (Θ : Finset ℝ) (qSq : Finset F → ℝ)
    (hResidualStable : ∀ u ∈ G, ∀ b ∈ residualNonzeroFreqs (F := F) T,
      u * b ∈ residualNonzeroFreqs (F := F) T)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ residualNonzeroFreqs (F := F) T,
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)) :
    RawResidualTailLeCosetScale ψ G σ T (residualOrbitCarrier (F := F) G T) qSq Θ := by
  intro θ hθ
  let B : Finset F :=
    (residualNonzeroFreqs (F := F) T).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)
  have hB0 : (0 : F) ∉ B := by
    intro h0
    have h0res : (0 : F) ∈ residualNonzeroFreqs (F := F) T := (Finset.mem_filter.mp h0).1
    unfold residualNonzeroFreqs at h0res
    have h0nz : (0 : F) ∈ nonzeroFreqs (F := F) := (Finset.mem_filter.mp h0res).1
    rw [mem_nonzeroFreqs] at h0nz
    exact h0nz rfl
  have hBstable : ∀ u ∈ G, ∀ x ∈ B, u * x ∈ B := by
    intro u hu x hx
    have hx' := Finset.mem_filter.mp hx
    have hxRes : x ∈ residualNonzeroFreqs (F := F) T := hx'.1
    have hxTail : θ ≤ ‖eta ψ G x‖ ^ 2 / σ ^ 2 := hx'.2
    exact Finset.mem_filter.mpr
      ⟨hResidualStable u hu x hxRes,
        normalizedSq_superlevel_stable_of_finSubgroup ψ hG hu hxTail⟩
  have hcard := ArkLib.ProximityGap.E2DilationDirectCount.badScalarSet_card_eq_orbit_mul
    hG hB0 hBstable
  have himage_subset :
      B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b) ⊆
        (residualOrbitCarrier (F := F) G T).filter (fun O => θ ≤ qSq O) := by
    intro O hO
    rw [Finset.mem_image] at hO
    obtain ⟨b, hbB, rfl⟩ := hO
    have hb' := Finset.mem_filter.mp hbB
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem
          (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b) hb'.1,
        hqSq θ hθ b hb'.1 hb'.2⟩
  have hcardImageLe :
      (B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)).card ≤
        ((residualOrbitCarrier (F := F) G T).filter (fun O => θ ≤ qSq O)).card :=
    Finset.card_le_card himage_subset
  have hnat :
      B.card ≤ G.card *
        ((residualOrbitCarrier (F := F) G T).filter (fun O => θ ≤ qSq O)).card := by
    rw [hcard,
      Nat.mul_comm (B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)).card
        G.card]
    exact Nat.mul_le_mul_left G.card hcardImageLe
  exact_mod_cast hnat

/-- A quotient residual tail plus the residual orbit lift gives the raw
residual tail required by the R234 top-rank consumer. -/
theorem residualNormalizedSqGridTail_of_quotient_residual
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (T : Finset F) (Qres : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (hLift : RawResidualTailLeCosetScale ψ G σ T Qres qSq Θ)
    (hQTail : QuotientResidualGridTail Qres qSq Θ Bq) :
    ResidualNormalizedSqGridTail ψ G σ T Θ
      (fun θ => (G.card : ℝ) * Bq θ) := by
  intro θ hθ
  calc
    ((((residualNonzeroFreqs (F := F) T).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Qres.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ
    _ ≤ (G.card : ℝ) * Bq θ :=
      mul_le_mul_of_nonneg_left (hQTail θ hθ) (Nat.cast_nonneg _)

/-- Quotient-facing R234 endpoint.  Direct top payment remains on the raw
nonzero frequencies, while the residual tail may be proved on a quotient
carrier and lifted with multiplicity `|G|`. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_topRank_quotient_residual_tail
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (T : Finset F) (Qres : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) (δ Bq : ℝ → ℝ) (Atop : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hTop :
      (∑ b ∈ topNonzeroFreqs (F := F) T,
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2))) ≤ Atop)
    (hstairResidual : ∀ b ∈ residualNonzeroFreqs (F := F) T,
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hLift : RawResidualTailLeCosetScale ψ G σ T Qres qSq Θ)
    (hQTail : QuotientResidualGridTail Qres qSq Θ Bq)
    (hweighted :
      Atop + (∑ θ ∈ Θ, δ θ * ((G.card : ℝ) * Bq θ))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_topRank_residual_tail
    ψ G T Θ δ (fun θ => (G.card : ℝ) * Bq θ) Atop
    hδ hTop hstairResidual
    (residualNormalizedSqGridTail_of_quotient_residual
      ψ G T Qres qSq Θ Bq hLift hQTail)
    hweighted

/-- Natural residual-orbit endpoint: the residual quotient carrier is the image
of the raw residual frequencies under the `G`-orbit map, and the residual lift
is supplied by Gauss-period orbit invariance plus residual-carrier stability. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_topRank_natural_quotient_residual_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (T : Finset F) (qSq : Finset F → ℝ)
    (Θ : Finset ℝ) (δ Bq : ℝ → ℝ) (Atop : ℝ)
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hResidualStable : ∀ u ∈ G, ∀ b ∈ residualNonzeroFreqs (F := F) T,
      u * b ∈ residualNonzeroFreqs (F := F) T)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ residualNonzeroFreqs (F := F) T,
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hTop :
      (∑ b ∈ topNonzeroFreqs (F := F) T,
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2))) ≤ Atop)
    (hstairResidual : ∀ b ∈ residualNonzeroFreqs (F := F) T,
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hQTail :
      QuotientResidualGridTail (residualOrbitCarrier (F := F) G T) qSq Θ Bq)
    (hweighted :
      Atop + (∑ θ ∈ Θ, δ θ * ((G.card : ℝ) * Bq θ))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_topRank_quotient_residual_tail
    ψ G T (residualOrbitCarrier (F := F) G T) qSq Θ δ Bq Atop
    hδ hTop hstairResidual
    (rawResidualTailLeCosetScale_of_gauss_residual_orbit_score
      ψ G T hG Θ qSq hResidualStable hqSq)
    hQTail hweighted

end

end ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift.rawResidualTailLeCosetScale_of_gauss_residual_orbit_score
#print axioms
  ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift.residualNormalizedSqGridTail_of_quotient_residual
#print axioms
  ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift.nonzeroNormalizedSqQuarterMGFResidual_of_topRank_quotient_residual_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R235QuotientResidualTailLift.nonzeroNormalizedSqQuarterMGFResidual_of_topRank_natural_quotient_residual_tail
