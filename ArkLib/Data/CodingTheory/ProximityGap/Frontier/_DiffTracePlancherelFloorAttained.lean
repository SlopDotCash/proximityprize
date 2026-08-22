/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTracePlancherelFloor

/-!
# EXTEND — the equality case of the variance-core Plancherel floor (#444)

**Frontier-movement extension of `_DiffTracePlancherelFloor`.**  That file proved the exact value
`(DiffTrace θ Rel).re = ‖Σ_T Jphase θ T‖² − #Rel` and the unconditional FLOOR
`(DiffTrace θ Rel).re ≥ −#Rel` (the off-diagonal first moment drops at most `#Rel` below zero,
because the shifted object `(DiffTrace).re + #Rel = ‖Σ Jphase‖²` is a non-negative square).

This file pins the **equality case** of that floor — the exact certificate for when the variance
core sits ON its floor — without touching the open prize UPPER bound.

## The equality case

Since `(DiffTrace θ Rel).re + #Rel = ‖Σ_T Jphase θ T‖²` and a squared modulus vanishes iff its base
vanishes (`Complex.normSq_eq_zero`):
```
   (DiffTrace θ Rel).re = −#Rel   ⟺   ‖Σ_T Jphase θ T‖² = 0   ⟺   Σ_T Jphase θ T = 0.
```
So the variance-core off-diagonal trace attains its absolute floor `−#Rel` **exactly when the linear
phase sum perfectly cancels** (`Σ_T Jphase θ T = 0`).  Conversely, any non-vanishing linear phase
sum lifts the trace STRICTLY off the floor (`−#Rel < (DiffTrace).re`).  This is the sharp two-sided
companion to `diffTrace_re_ge_neg_card`: the floor is not merely a bound but is attained on an
explicit, checkable, codimension-(real) cancellation event.

## What this file PROVES (axiom-clean, no `sorry`)

* `diffTrace_re_eq_neg_card_iff_sum_eq_zero` — `(DiffTrace).re = −#Rel ⟺ Σ_T Jphase θ T = 0`;
* `diffTrace_re_eq_neg_card_of_sum_eq_zero` — perfect cancellation ⟹ trace on the floor;
* `sum_eq_zero_of_diffTrace_re_eq_neg_card` — trace on the floor ⟹ perfect cancellation;
* `diffTrace_re_gt_neg_card_of_sum_ne_zero` — non-vanishing phase sum ⟹ trace STRICTLY above floor;
* `diffTrace_re_eq_neg_card_add_normSq` — the exact shifted-square value
  `(DiffTrace).re = −#Rel + ‖Σ Jphase‖²` (floor + non-negative excess).

NO CORE / cancellation-of-the-prize / completion / moment-saving / capacity / upper-bound claim:
this is the equality CASE of the FLOOR side.  The prize needs the still-open UPPER bound on
`‖Σ Jphase‖²`; here we only characterise when the closed lower end is met.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The exact shifted-square value (floor + non-negative excess) -/

/-- **`diffTrace_re_eq_neg_card_add_normSq`** — the off-diagonal first-moment real part is its
absolute floor `−#Rel` PLUS the non-negative squared-modulus excess `‖Σ_T Jphase θ T‖²`.  This is
just `diffTrace_re_eq_normSq_sub_card` written in floor-plus-excess form. -/
theorem diffTrace_re_eq_neg_card_add_normSq (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re
      = -(Rel.card : ℝ) + Complex.normSq (∑ T ∈ Rel, Jphase θ T) := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]; ring

/-! ## §2 The equality case of the floor -/

/-- **`diffTrace_re_eq_neg_card_of_sum_eq_zero`** — if the linear phase sum perfectly cancels
(`Σ_T Jphase θ T = 0`), then the variance-core off-diagonal trace sits exactly on its floor
`−#Rel`. -/
theorem diffTrace_re_eq_neg_card_of_sum_eq_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hsum : (∑ T ∈ Rel, Jphase θ T) = 0) :
    (DiffTrace θ Rel).re = -(Rel.card : ℝ) := by
  rw [diffTrace_re_eq_neg_card_add_normSq hmul hone hunit Rel, hsum]
  simp

/-- **`sum_eq_zero_of_diffTrace_re_eq_neg_card`** — conversely, if the off-diagonal trace attains its
floor `−#Rel`, then the linear phase sum perfectly cancels (`Σ_T Jphase θ T = 0`).  Uses
`Complex.normSq_eq_zero`: a squared modulus vanishes iff its base does. -/
theorem sum_eq_zero_of_diffTrace_re_eq_neg_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hfloor : (DiffTrace θ Rel).re = -(Rel.card : ℝ)) :
    (∑ T ∈ Rel, Jphase θ T) = 0 := by
  have hval := diffTrace_re_eq_neg_card_add_normSq hmul hone hunit Rel
  rw [hfloor] at hval
  have hnsq : Complex.normSq (∑ T ∈ Rel, Jphase θ T) = 0 := by linarith
  exact Complex.normSq_eq_zero.mp hnsq

/-- **`diffTrace_re_eq_neg_card_iff_sum_eq_zero`** — the sharp equality case: the variance-core
off-diagonal trace attains its absolute floor `−#Rel` IF AND ONLY IF the linear phase sum perfectly
cancels.  This is the two-sided companion to `diffTrace_re_ge_neg_card`: the floor is attained on an
explicit, checkable, perfect-cancellation event `Σ_T Jphase θ T = 0`. -/
theorem diffTrace_re_eq_neg_card_iff_sum_eq_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re = -(Rel.card : ℝ) ↔ (∑ T ∈ Rel, Jphase θ T) = 0 := by
  constructor
  · exact sum_eq_zero_of_diffTrace_re_eq_neg_card hmul hone hunit Rel
  · exact diffTrace_re_eq_neg_card_of_sum_eq_zero hmul hone hunit Rel

/-! ## §3 Strict lift off the floor -/

/-- **`diffTrace_re_gt_neg_card_of_sum_ne_zero`** — any non-vanishing linear phase sum lifts the
off-diagonal trace STRICTLY above its floor: `−#Rel < (DiffTrace θ Rel).re`.  Contrapositive of the
equality case; the excess is the strictly-positive square `‖Σ_T Jphase θ T‖² > 0`. -/
theorem diffTrace_re_gt_neg_card_of_sum_ne_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hsum : (∑ T ∈ Rel, Jphase θ T) ≠ 0) :
    -(Rel.card : ℝ) < (DiffTrace θ Rel).re := by
  rw [diffTrace_re_eq_neg_card_add_normSq hmul hone hunit Rel]
  have hpos : 0 < Complex.normSq (∑ T ∈ Rel, Jphase θ T) := by
    rcases (Complex.normSq_nonneg (∑ T ∈ Rel, Jphase θ T)).lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.normSq_eq_zero.mp h.symm) hsum
  linarith

end ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained.diffTrace_re_eq_neg_card_add_normSq
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained.diffTrace_re_eq_neg_card_of_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained.sum_eq_zero_of_diffTrace_re_eq_neg_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained.diffTrace_re_eq_neg_card_iff_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained.diffTrace_re_gt_neg_card_of_sum_ne_zero
