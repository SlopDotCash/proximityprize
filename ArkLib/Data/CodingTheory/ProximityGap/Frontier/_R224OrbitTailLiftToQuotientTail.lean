/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R224 orbit-tail lift)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223QuotientTailToScaledSpikePrize
import ArkLib.Data.CodingTheory.ProximityGap.E2DilationDirectCount

/-!
# R224 (#466): orbit-tail lift for quotient certificates

R223 consumes an abstract raw-to-quotient tail lift.  This file proves that lift
from the standard finite-subgroup orbit partition: if each raw normalized-square
superlevel set is stable under the multiplicative subgroup action, then its
cardinality is `|G|` times its orbit count, hence bounded by `|G|` times any
quotient survivor set containing those orbits.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The quotient carrier of nonzero frequencies by multiplicative `G`-orbits. -/
def nonzeroOrbitCarrier (G : Finset F) : Finset (Finset F) :=
  (nonzeroFreqs (F := F)).image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)

/-- If raw normalized-square superlevel sets are stable under multiplication by
`G`, then their raw cardinality is bounded by `|G|` times the corresponding
orbit-survivor count.  The quotient score `qSq` only needs to dominate the orbit
of each raw survivor. -/
theorem rawNonzeroTailLeCosetScale_of_orbit_superlevels
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G) (Θ : Finset ℝ) (qSq : Finset F → ℝ)
    (hstable : ∀ θ ∈ Θ, ∀ u ∈ G, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ ‖eta ψ G (u * b)‖ ^ 2 / σ ^ 2)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 → θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)) :
    RawNonzeroTailLeCosetScale ψ G σ (nonzeroOrbitCarrier (F := F) G) qSq Θ := by
  intro θ hθ
  let B : Finset F :=
    (nonzeroFreqs (F := F)).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)
  have hB0 : (0 : F) ∉ B := by
    intro h0
    have h0nz : (0 : F) ∈ nonzeroFreqs (F := F) := (Finset.mem_filter.mp h0).1
    rw [mem_nonzeroFreqs] at h0nz
    exact h0nz rfl
  have hBstable : ∀ u ∈ G, ∀ x ∈ B, u * x ∈ B := by
    intro u hu x hx
    have hx' := Finset.mem_filter.mp hx
    have hxNon : x ∈ nonzeroFreqs (F := F) := hx'.1
    have hxTail : θ ≤ ‖eta ψ G x‖ ^ 2 / σ ^ 2 := hx'.2
    have hu0 : u ≠ 0 := ArkLib.ProximityGap.E2DilationDirectCount.ne_zero_of_mem_finSubgroup hG hu
    have hx0 : x ≠ 0 := by
      rw [mem_nonzeroFreqs] at hxNon
      exact hxNon
    have huxNon : u * x ∈ nonzeroFreqs (F := F) := by
      rw [mem_nonzeroFreqs]
      exact mul_ne_zero hu0 hx0
    exact Finset.mem_filter.mpr
      ⟨huxNon, hstable θ hθ u hu x hxNon hxTail⟩
  have hcard := ArkLib.ProximityGap.E2DilationDirectCount.badScalarSet_card_eq_orbit_mul hG hB0 hBstable
  have himage_subset :
      B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b) ⊆
        (nonzeroOrbitCarrier (F := F) G).filter (fun O => θ ≤ qSq O) := by
    intro O hO
    rw [Finset.mem_image] at hO
    obtain ⟨b, hbB, rfl⟩ := hO
    have hb' := Finset.mem_filter.mp hbB
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b) hb'.1,
        hqSq θ hθ b hb'.1 hb'.2⟩
  have hcardImageLe :
      (B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)).card ≤
        ((nonzeroOrbitCarrier (F := F) G).filter (fun O => θ ≤ qSq O)).card :=
    Finset.card_le_card himage_subset
  have hnat :
      B.card ≤ G.card *
        ((nonzeroOrbitCarrier (F := F) G).filter (fun O => θ ≤ qSq O)).card := by
    rw [hcard, Nat.mul_comm (B.image (fun b => ArkLib.ProximityGap.E2DilationDirectCount.orbit G b)).card G.card]
    exact Nat.mul_le_mul_left G.card hcardImageLe
  exact_mod_cast hnat

end

end ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail.rawNonzeroTailLeCosetScale_of_orbit_superlevels
