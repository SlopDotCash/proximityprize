/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessRatio
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTracePlancherelFloorAttained
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceTrivialEnvelope

/-!
# EXTEND — the exact range and both extremes of the dimensionless flatness ratio (#444)

**Frontier-movement extension of `_DiffTraceFlatnessRatio`.**  That file introduced the dimensionless
L²-flatness ratio `ρ_flat(Rel) = ‖Σ_T Jphase θ T‖² / #Rel` and proved `ρ_flat ≥ 0` plus the
S-parameterized bound `ρ_flat ≤ 1 + S/#Rel ⟺ (off-diag 2nd moment).re ≤ S`.  This file pins the
ratio's EXACT RANGE and characterizes BOTH extremes (the dimensionless image of the floor/ceiling
attainment work).

## The range and its extremes

Since each `Jphase θ T` is a unit, `0 ≤ ‖Σ Jphase‖ ≤ #Rel`, so for nonempty `Rel`:
```
        0  ≤  ρ_flat(Rel) = ‖Σ Jphase‖²/#Rel  ≤  #Rel,
        with  ρ_flat = 0     ⟺  Σ_T Jphase θ T = 0       (perfect cancellation = perfect flatness),
              ρ_flat = #Rel  ⟺  ‖Σ_T Jphase θ T‖ = #Rel  (perfect coherence = maximal flatness ratio).
```
So the prize-facing normalization lives in `[0, #Rel]`; the orthonormal/diagonal target `ρ_flat ≈ 1`
(square-root cancellation) sits a factor `#Rel` below the maximally-coherent top and a unit above the
perfectly-cancelled bottom.  The bottom is the perfect-cancellation event, the top the
perfect-coherence event — the dimensionless image of the variance-core floor/ceiling.

## What this file PROVES (axiom-clean, no `sorry`)

* `flatnessRatio_le_card` — `ρ_flat ≤ #Rel` (triangle ceiling, dimensionless);
* `flatnessRatio_mem_range` — `0 ≤ ρ_flat ≤ #Rel`;
* `flatnessRatio_eq_zero_iff_sum_eq_zero` — bottom `ρ_flat = 0 ⟺ Σ Jphase = 0` (for #Rel > 0);
* `flatnessRatio_eq_card_iff_norm_eq_card` — top `ρ_flat = #Rel ⟺ ‖Σ Jphase‖ = #Rel` (for #Rel > 0).

NO CORE / cancellation / completion / moment-saving / capacity claim: only the range and extreme cases
of the dimensionless normalization.  The prize content (`ρ_flat ≤ 1 + o(1)`) is untouched.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The dimensionless triangle ceiling and range -/

/-- **`flatnessRatio_le_card`** — the flatness ratio is at most `#Rel`, the dimensionless image of the
triangle envelope `‖Σ Jphase‖ ≤ #Rel` (so `‖Σ Jphase‖² ≤ #Rel²`, divided by `#Rel`). -/
theorem flatnessRatio_le_card (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_le_iff₀ hne]
  have h := linearPhase_normSq_le_card_sq (θ := θ) hunit Rel
  nlinarith [h]

/-- **`flatnessRatio_mem_range`** — `0 ≤ ρ_flat ≤ #Rel` (nonempty `Rel`). -/
theorem flatnessRatio_mem_range (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    0 ≤ flatnessRatio θ Rel ∧ flatnessRatio θ Rel ≤ (Rel.card : ℝ) :=
  ⟨flatnessRatio_nonneg Rel, flatnessRatio_le_card hunit Rel hne⟩

/-! ## §2 The two extremes -/

/-- **`flatnessRatio_eq_zero_iff_sum_eq_zero`** — the flatness ratio hits its BOTTOM `0` iff the
aggregate phase sum perfectly cancels (`Σ_T Jphase θ T = 0`).  The dimensionless image of the
floor-attainment case. -/
theorem flatnessRatio_eq_zero_iff_sum_eq_zero (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel = 0 ↔ (∑ T ∈ Rel, Jphase θ T) = 0 := by
  unfold flatnessRatio
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact Complex.normSq_eq_zero.mp h
    · exact absurd h (ne_of_gt hne)
  · intro h; left; rw [h]; simp

/-- **`flatnessRatio_eq_card_iff_norm_eq_card`** — the flatness ratio hits its TOP `#Rel` iff the
aggregate phase sum is maximally coherent (`‖Σ_T Jphase θ T‖ = #Rel`).  The dimensionless image of the
ceiling-attainment case. -/
theorem flatnessRatio_eq_card_iff_norm_eq_card (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel = (Rel.card : ℝ) ↔ ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_eq_iff (ne_of_gt hne), Complex.normSq_eq_norm_sq]
  have hc : 0 ≤ (Rel.card : ℝ) := le_of_lt hne
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  constructor
  · intro h
    -- ‖Σ‖² = #Rel·#Rel = #Rel², and ‖Σ‖,#Rel ≥ 0, so ‖Σ‖ = #Rel
    have hsq : ‖∑ T ∈ Rel, Jphase θ T‖ ^ 2 = (Rel.card : ℝ) ^ 2 := by ring_nf; nlinarith [h]
    nlinarith [hsq, hn, hc, sq_nonneg (‖∑ T ∈ Rel, Jphase θ T‖ - (Rel.card : ℝ))]
  · intro h; rw [h]; ring

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange.flatnessRatio_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange.flatnessRatio_mem_range
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange.flatnessRatio_eq_zero_iff_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange.flatnessRatio_eq_card_iff_norm_eq_card
