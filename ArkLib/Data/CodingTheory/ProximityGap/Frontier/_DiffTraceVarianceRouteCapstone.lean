/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceReframeCircularity

/-!
# CAPSTONE — the variance route as ONE end-to-end consumer: L²-flatness ⟹ off-diagonal second moment (#444)

**Variance-route capstone (citable deliverable).**  This file packages the four-brick variance-core
arc (`_NextDifferenceVariety` → `_DiffTraceDiagonalExtraction` → `_DiffTracePlancherelFloor` →
`_DiffTraceLinearSumReframe`/`_DiffTraceReframeCircularity`) into a SINGLE end-to-end theorem and an
exact characterization, so downstream work can cite ONE statement instead of re-tracing the chain.

## The single capstone — `linearSumFlatness_to_secondMoment`

A direct **L²-flatness** bound on the aggregate linear phase sum,
```
        ‖Σ_T Jphase θ T‖²  ≤  #Rel + S,
```
implies the off-diagonal second-moment real-part bound the variance core needs:
```
        (Σ_T Σ_{T'≠T} Jphase θ T · conj (Jphase θ T')).re  ≤  S.
```
Proof chain (all kernel-checked rungs): L²-flatness ⟺ `FirstMomentDiffCancellation`
(`firstMomentDiffCancellation_of_normSq_le`) ⟹ off-diagonal second moment
(`firstMoment_to_secondMoment_bound`).  The `√p` is gone (each `Jphase` a unit), the variety/pair
structure is collapsed (Plancherel), and what remains is exactly an L²-flatness inequality on a
single complex number.

## The exact characterization — `secondMoment_re_eq_normSq_sub_card`

Better than an implication: the off-diagonal second moment is EXACTLY pinned:
```
        (Σ_T Σ_{T'≠T} Jphase θ T · conj (Jphase θ T')).re  =  ‖Σ_T Jphase θ T‖²  −  #Rel.
```
So the variance-route open core is, with NO slack lost anywhere in the chain, the single quantity
`‖Σ_T Jphase θ T‖² − #Rel`.  Bounding it `≤ S` ⟺ `‖Σ Jphase‖² ≤ #Rel + S`.

## What this file PROVES (axiom-clean, no `sorry`)

* `secondMoment_re_eq_normSq_sub_card` — the off-diagonal second moment real part EQUALS
  `‖Σ Jphase‖² − #Rel` (the exact, slack-free characterization);
* `linearSumFlatness_to_secondMoment` — L²-flatness `‖Σ Jphase‖² ≤ #Rel + S` ⟹ the off-diagonal
  second-moment real-part bound `≤ S` (the single end-to-end consumer);
* `secondMoment_re_le_iff_normSq_le` — the iff form (exact equivalence of the two bounds).

NO CORE / cancellation / completion / moment-saving / capacity claim: the L²-flatness inequality is
NOT proved.  This is the citable end-to-end reduction of the variance route to a single L²-flatness
statement on the aggregate iterated Jacobi phase.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`secondMoment_re_eq_normSq_sub_card`** — the EXACT, slack-free characterization: the
off-diagonal second-moment real part equals `‖Σ_T Jphase θ T‖² − #Rel`.  Combines
`diffTrace_eq_secondMoment` (second moment = `DiffTrace`) with the Plancherel value
`diffTrace_re_eq_normSq_sub_card`. -/
theorem secondMoment_re_eq_normSq_sub_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re
      = Complex.normSq (∑ T ∈ Rel, Jphase θ T) - (Rel.card : ℝ) := by
  rw [← diffTrace_eq_secondMoment hmul hone hunit Rel]
  exact diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel

/-- **`linearSumFlatness_to_secondMoment`** — THE single end-to-end consumer.  An L²-flatness bound
on the aggregate linear phase sum, `‖Σ_T Jphase θ T‖² ≤ #Rel + S`, implies the off-diagonal
second-moment real-part bound `≤ S` the variance core needs.  One citable rung for the whole
variance-route chain. -/
theorem linearSumFlatness_to_secondMoment (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) + S) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S := by
  have hcore : FirstMomentDiffCancellation θ Rel S :=
    firstMomentDiffCancellation_of_normSq_le hmul hone hunit Rel S h
  exact firstMoment_to_secondMoment_bound hmul hone hunit Rel S hcore

/-- **`secondMoment_re_le_iff_normSq_le`** — the iff form: the off-diagonal second-moment real-part
bound `≤ S` is EXACTLY the L²-flatness bound `‖Σ Jphase‖² ≤ #Rel + S` (no slack lost). -/
theorem secondMoment_re_le_iff_normSq_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) + S := by
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel]
  constructor <;> intro h <;> linarith

end ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone.secondMoment_re_eq_normSq_sub_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone.linearSumFlatness_to_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone.secondMoment_re_le_iff_normSq_le
