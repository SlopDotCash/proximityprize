/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceEnvelopeCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceVarianceRouteCapstone

/-!
# BRIDGE — transfer the variance-core envelope+attainment to the NAMED second-moment object (#444)

`_DiffTraceEnvelopeCapstone` characterized the enclosure `(DiffTrace θ Rel).re ∈ [−#Rel, #Rel²−#Rel]`
and both attainment cases (floor ⟺ `Σ Jphase = 0`, ceiling ⟺ `‖Σ Jphase‖ = #Rel`).
`_DiffTraceVarianceRouteCapstone` proved the identification `secondMoment_re = ‖Σ Jphase‖² − #Rel`
(the off-diagonal SECOND MOMENT `Σ_T Σ_{T'≠T} Jphase θ T · conj (Jphase θ T')` is the variance-route's
named object).  This file transports the envelope + attainment directly onto that named object, so
downstream variance-route work cites ONE statement about the actual second moment, with no need to
re-identify it with `DiffTrace`.

## What this file PROVES (axiom-clean, no `sorry`)

For `Q θ Rel := (Σ_T Σ_{T'∈Rel.erase T} Jphase θ T · conj (Jphase θ T')).re` (the off-diagonal second
moment real part):

* `secondMoment_re_mem_envelope` — `−#Rel ≤ Q ≤ #Rel² − #Rel`;
* `secondMoment_re_eq_neg_card_iff_sum_eq_zero` — floor `Q = −#Rel` ⟺ `Σ_T Jphase θ T = 0`;
* `secondMoment_re_eq_ceiling_iff_norm_eq_card` — ceiling `Q = #Rel²−#Rel` ⟺ `‖Σ_T Jphase θ T‖ = #Rel`;
* `secondMoment_re_le_iff_norm_le` — at equal piece count, second-moment order ⟺ aggregate-coherence order.

NO CORE / cancellation / completion / moment-saving / capacity / sub-Poisson-upper claim: pure transport
of the closed envelope and its equality cases onto the named second-moment object.  The open prize
content (a sub-Poisson UPPER bound on the second moment / on `‖Σ Jphase‖²`) is untouched.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained
open ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- Off-diagonal second-moment real part — the variance-route's named object. -/
noncomputable def secondMomentRe (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℝ :=
  (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re

/-- The named second-moment real part equals the variance-core trace real part exactly, via
`secondMoment_re_eq_normSq_sub_card` and `diffTrace_re_eq_normSq_sub_card`. -/
theorem secondMomentRe_eq_diffTrace_re (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    secondMomentRe θ Rel = (DiffTrace θ Rel).re := by
  unfold secondMomentRe
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel,
      diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]

/-! ## §1 Envelope on the named object -/

/-- **`secondMoment_re_mem_envelope`** — `−#Rel ≤ secondMomentRe ≤ #Rel² − #Rel`. -/
theorem secondMoment_re_mem_envelope (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    -(Rel.card : ℝ) ≤ secondMomentRe θ Rel
      ∧ secondMomentRe θ Rel ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) := by
  rw [secondMomentRe_eq_diffTrace_re hmul hone hunit Rel]
  exact ⟨diffTrace_re_ge_neg_card hmul hone hunit Rel,
    diffTrace_re_le_card_sq_sub_card hmul hone hunit Rel⟩

/-! ## §2 Attainment cases on the named object -/

/-- **`secondMoment_re_eq_neg_card_iff_sum_eq_zero`** — the named second moment attains its floor
`−#Rel` iff the aggregate phase sum perfectly cancels. -/
theorem secondMoment_re_eq_neg_card_iff_sum_eq_zero
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    secondMomentRe θ Rel = -(Rel.card : ℝ) ↔ (∑ T ∈ Rel, Jphase θ T) = 0 := by
  rw [secondMomentRe_eq_diffTrace_re hmul hone hunit Rel]
  exact diffTrace_re_eq_neg_card_iff_sum_eq_zero hmul hone hunit Rel

/-- **`secondMoment_re_eq_ceiling_iff_norm_eq_card`** — the named second moment attains its trivial
ceiling `#Rel²−#Rel` iff the aggregate phase sum is maximally coherent. -/
theorem secondMoment_re_eq_ceiling_iff_norm_eq_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    secondMomentRe θ Rel = (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ) := by
  rw [secondMomentRe_eq_diffTrace_re hmul hone hunit Rel]
  exact diffTrace_re_eq_ceiling_iff_norm_eq_card hmul hone hunit Rel

/-! ## §3 Fixed-piece-count order-iso on the named object -/

/-- **`secondMoment_re_le_iff_norm_le`** — at equal piece count, the named second moment ranks configs
exactly by aggregate phase coherence. -/
theorem secondMoment_re_le_iff_norm_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel₁ Rel₂ : Finset (Fin r → R))
    (hcard : Rel₁.card = Rel₂.card) :
    secondMomentRe θ Rel₁ ≤ secondMomentRe θ Rel₂
      ↔ ‖∑ T ∈ Rel₁, Jphase θ T‖ ≤ ‖∑ T ∈ Rel₂, Jphase θ T‖ := by
  rw [secondMomentRe_eq_diffTrace_re hmul hone hunit Rel₁,
      secondMomentRe_eq_diffTrace_re hmul hone hunit Rel₂]
  exact ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_le_iff_norm_le
    hmul hone hunit Rel₁ Rel₂ hcard

end ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope.secondMomentRe_eq_diffTrace_re
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope.secondMoment_re_mem_envelope
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope.secondMoment_re_eq_neg_card_iff_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope.secondMoment_re_eq_ceiling_iff_norm_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope.secondMoment_re_le_iff_norm_le
