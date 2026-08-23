/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceTrivialEnvelope

/-!
# EXTEND — the equality case of the variance-core trivial CEILING (#444)

**Frontier-movement extension of `_DiffTraceTrivialEnvelope`.**  That file proved the unconditional
trivial CEILING `(DiffTrace θ Rel).re ≤ #Rel² − #Rel`, from the triangle envelope
`‖Σ_T Jphase θ T‖ ≤ #Rel` on the unit-phase aggregate sum.  Together with the Plancherel FLOOR
(`_DiffTracePlancherelFloor`, `_DiffTracePlancherelFloorAttained`) this places the variance-core
off-diagonal trace in `[−#Rel, #Rel²−#Rel]`.

This file pins the EQUALITY CASE of the CEILING — the exact dual of the floor-attainment file — WITHOUT
touching the open prize sub-Poisson UPPER saving.

## The equality case

Using the exact value `(DiffTrace θ Rel).re = ‖Σ Jphase‖² − #Rel` and squaring the triangle envelope:
```
   (DiffTrace θ Rel).re = #Rel² − #Rel   ⟺   ‖Σ_T Jphase θ T‖² = #Rel²   ⟺   ‖Σ_T Jphase θ T‖ = #Rel.
```
So the variance-core off-diagonal trace attains its trivial CEILING **exactly when the aggregate
unit-phase sum is maximally constructive** (`‖Σ Jphase‖ = #Rel`, i.e. the triangle inequality is an
equality — perfect coherence of all `#Rel` unit phases).  Conversely, any strict triangle deficit
`‖Σ Jphase‖ < #Rel` drops the trace STRICTLY below the ceiling.  This is the door-(iv) ρ=1 saturation
statement at the variance-core level, and the exact dual of the floor's perfect-cancellation case.

## What this file PROVES (axiom-clean, no `sorry`)

* `diffTrace_re_eq_ceiling_iff_normSq_eq_card_sq` — `(DiffTrace).re = #Rel²−#Rel ⟺ ‖Σ Jphase‖² = #Rel²`;
* `diffTrace_re_eq_ceiling_iff_norm_eq_card` — same, in un-squared form `‖Σ Jphase‖ = #Rel`;
* `diffTrace_re_eq_ceiling_of_norm_eq_card` — maximal coherence ⟹ trace on the ceiling;
* `diffTrace_re_lt_ceiling_of_norm_lt_card` — strict triangle deficit ⟹ trace STRICTLY below ceiling.

NO CORE / cancellation / completion / moment-saving / capacity / sub-Poisson-upper claim: this is the
equality CASE of the trivial CEILING side.  The prize needs the still-open improvement of the ceiling
to a genuine anti-concentration bound; here we only characterise when the trivial ceiling is met.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The ceiling-attainment equivalence (squared form) -/

/-- **`diffTrace_re_eq_ceiling_iff_normSq_eq_card_sq`** — the variance-core off-diagonal trace attains
its trivial ceiling `#Rel²−#Rel` IF AND ONLY IF the aggregate phase sum saturates the squared triangle
envelope `‖Σ Jphase‖² = #Rel²`.  Immediate from `(DiffTrace).re = ‖Σ Jphase‖² − #Rel`. -/
theorem diffTrace_re_eq_ceiling_iff_normSq_eq_card_sq
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re = (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) = (Rel.card : ℝ) ^ 2 := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]
  constructor <;> intro h <;> linarith

/-! ## §2 The ceiling-attainment equivalence (un-squared norm form) -/

/-- **`diffTrace_re_eq_ceiling_iff_norm_eq_card`** — un-squared form: the trace attains its trivial
ceiling IF AND ONLY IF the aggregate unit-phase sum is maximally constructive, `‖Σ Jphase‖ = #Rel`
(the triangle inequality is an equality).  Squared modulus `= #Rel²` is equivalent to norm `= #Rel`
since both sides are nonnegative. -/
theorem diffTrace_re_eq_ceiling_iff_norm_eq_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re = (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ) := by
  rw [diffTrace_re_eq_ceiling_iff_normSq_eq_card_sq hmul hone hunit Rel,
      Complex.normSq_eq_norm_sq]
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  have hc : 0 ≤ (Rel.card : ℝ) := by positivity
  constructor
  · intro h; nlinarith
  · intro h; rw [h]

/-! ## §3 Sufficiency and strict drop below the ceiling -/

/-- **`diffTrace_re_eq_ceiling_of_norm_eq_card`** — maximal phase coherence (`‖Σ Jphase‖ = #Rel`)
⟹ the trace sits exactly on its trivial ceiling. -/
theorem diffTrace_re_eq_ceiling_of_norm_eq_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hnorm : ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ)) :
    (DiffTrace θ Rel).re = (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) :=
  (diffTrace_re_eq_ceiling_iff_norm_eq_card hmul hone hunit Rel).mpr hnorm

/-- **`diffTrace_re_lt_ceiling_of_norm_lt_card`** — any strict triangle deficit
(`‖Σ Jphase‖ < #Rel`) drops the variance-core trace STRICTLY below its trivial ceiling.  The drop is
exactly the squared deficit `#Rel² − ‖Σ Jphase‖² > 0`. -/
theorem diffTrace_re_lt_ceiling_of_norm_lt_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hnorm : ‖∑ T ∈ Rel, Jphase θ T‖ < (Rel.card : ℝ)) :
    (DiffTrace θ Rel).re < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel, Complex.normSq_eq_norm_sq]
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  have hc : 0 ≤ (Rel.card : ℝ) := by positivity
  nlinarith

end ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained.diffTrace_re_eq_ceiling_iff_normSq_eq_card_sq
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained.diffTrace_re_eq_ceiling_iff_norm_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained.diffTrace_re_eq_ceiling_of_norm_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained.diffTrace_re_lt_ceiling_of_norm_lt_card
