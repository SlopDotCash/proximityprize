/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarSecondPinF17

/-!
# The second pin, widened: `δ* = 1/4` on `ε* ∈ [2/17, 6/17)` (#357, item 6/25)

The landed second pin (`DeltaStarSecondPinF17`) certifies `mcaDeltaStar = 1/4` for
`ε* ∈ [2/17, 3/17)` from three bad scalars at one deviation stack.  The band-3 sweep
found a richer stack: `v₀ = (1, 0⁶, 11)`, `v₁ = (1, 2, 0⁶)` carries **six** bad
scalars `γ ∈ {0, 10, 11, 14, 15, 16}` at `δ = 1/4` (each verified here by an explicit
6-point witness and explaining cubic; the no-joint side is the same root-counting
kill — any explanation of `v₁` on four of its zero positions is the zero codeword,
contradicting `v₁` at a support point of the witness).

Hence `ε_mca(C84, 1/4) ≥ 6/17`, and the pin window **doubles**:

  `mcaDeltaStar(C84, ε*) = 1/4` for every `ε* ∈ [2/17, 6/17)`.

The good side is inherited verbatim from the landed bands 1–2.  The wt-2 deviation
family is exhausted at six (targeted probe, normalized scan); any further widening
needs weight-3 patterns.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger

namespace ProximityGap.DeltaStarSecondPin

/-! ## The richer deviation stack -/

/-- The widened stack's first row: spikes at positions 0 and 7. -/
def v₀ : Fin 8 → F17 := ![1, 0, 0, 0, 0, 0, 0, 11]

/-- The second row: weight-2 deviation `(1, 2, 0, …, 0)`. -/
def v₁ : Fin 8 → F17 := ![1, 2, 0, 0, 0, 0, 0, 0]

/-- The joint-failure engine for the widened stack: any explanation of `v₁` on a
witness containing four of its zero positions is the zero codeword — contradicting
`v₁ i₀ ≠ 0` at a support point `i₀` of the witness. -/
theorem no_joint_on_v (T : Finset (Fin 8)) (i0 : Fin 8) (h0 : i0 ∈ T)
    (hne : v₁ i0 ≠ 0)
    (i1 i2 i3 i4 : Fin 8) (hz : v₁ i1 = 0 ∧ v₁ i2 = 0 ∧ v₁ i3 = 0 ∧ v₁ i4 = 0)
    (hmem : i1 ∈ T ∧ i2 ∈ T ∧ i3 ∈ T ∧ i4 ∈ T)
    (hcard : ({dom i1, dom i2, dom i3, dom i4} : Finset F17).card = 4) :
    ¬ pairJointAgreesOn (C84 : Set (Fin 8 → F17)) T v₀ v₁ := by
  rintro ⟨c₀, hc₀, c₁, hc₁, hag⟩
  have hvz : c₁ = 0 := by
    refine codeword_eq_zero_of_vanishing c₁ hc₁ {dom i1, dom i2, dom i3, dom i4}
      (le_of_eq hcard.symm) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨i1, rfl, by rw [(hag i1 hmem.1).2, hz.1]⟩
    · exact ⟨i2, rfl, by rw [(hag i2 hmem.2.1).2, hz.2.1]⟩
    · exact ⟨i3, rfl, by rw [(hag i3 hmem.2.2.1).2, hz.2.2.1]⟩
    · exact ⟨i4, rfl, by rw [(hag i4 hmem.2.2.2).2, hz.2.2.2]⟩
  have h1 := (hag i0 h0).2
  rw [hvz] at h1
  simp only [Pi.zero_apply] at h1
  exact hne h1.symm

/-! ## The six certificates (γ ∈ {0, 10, 11, 14, 15, 16}) -/

/-- **Certificate γ = 0**: witness `{1,2,3,4,5,6}`, line codeword `0`. -/
theorem vcert0 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 0 := by
  refine ⟨{1, 2, 3, 4, 5, 6}, card_clause (by decide), ⟨0, C84.zero_mem, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 1 (by decide) (by decide) 2 3 4 5 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Certificate γ = 10**: witness `{0,1,2,4,6,7}`, cubic `7 + 7x + 7x² + 7x³`. -/
theorem vcert10 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 10 := by
  refine ⟨{0, 1, 2, 4, 6, 7}, card_clause (by decide),
    ⟨_, cubic_mem 7 7 7 7, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 0 (by decide) (by decide) 2 4 6 7 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Certificate γ = 11**: witness `{0,1,4,5,6,7}`, cubic `10 + 9x + 13x² + 14x³`. -/
theorem vcert11 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 11 := by
  refine ⟨{0, 1, 4, 5, 6, 7}, card_clause (by decide),
    ⟨_, cubic_mem 10 9 13 14, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 0 (by decide) (by decide) 4 5 6 7 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Certificate γ = 14**: witness `{0,1,3,4,6,7}`, cubic `2 + 15x + 14x² + x³`. -/
theorem vcert14 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 14 := by
  refine ⟨{0, 1, 3, 4, 6, 7}, card_clause (by decide),
    ⟨_, cubic_mem 2 15 14 1, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 0 (by decide) (by decide) 3 4 6 7 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Certificate γ = 15**: witness `{0,1,2,3,5,7}`, cubic `6 + 5x + 15x² + 7x³`. -/
theorem vcert15 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 15 := by
  refine ⟨{0, 1, 2, 3, 5, 7}, card_clause (by decide),
    ⟨_, cubic_mem 6 5 15 7, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 0 (by decide) (by decide) 2 3 5 7 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Certificate γ = 16**: witness `{0,2,3,4,5,6}`, line codeword `0`. -/
theorem vcert16 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) v₀ v₁ 16 := by
  refine ⟨{0, 2, 3, 4, 5, 6}, card_clause (by decide), ⟨0, C84.zero_mem, ?_⟩, ?_⟩
  · intro i hi
    fin_cases hi <;> decide
  · exact no_joint_on_v _ 0 (by decide) (by decide) 2 3 4 5 (by decide)
      ⟨by decide, by decide, by decide, by decide⟩ (by decide)

/-- **Bad side, widened:** `ε_mca(C84, 1/4) ≥ 6/17`. -/
theorem epsMCA_quarter_ge_six :
    (6 / 17 : ℝ≥0∞) ≤ epsMCA (F := F17) (A := F17) (C84 : Set (Fin 8 → F17)) (1/4) := by
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C84 : Set (Fin 8 → F17)) (1/4) ![v₀, v₁]
    ({0, 10, 11, 14, 15, 16} : Finset F17) ?_
  · have hcard : ({0, 10, 11, 14, 15, 16} : Finset F17).card = 6 := by decide
    have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by
      rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
      norm_num
    rwa [hcard, hF] at h
  · intro γ hγ
    fin_cases hγ
    · simpa using vcert0
    · simpa using vcert10
    · simpa using vcert11
    · simpa using vcert14
    · simpa using vcert15
    · simpa using vcert16

/-! ## The widened pin -/

/-- **THE SECOND PIN, WIDENED.**  For `C = RS[F₁₇, ⟨2⟩, 4]` (smooth domain
`n = 8 = 2³`, rate `ρ = 1/2`) and every `ε* ∈ [2/17, 6/17)`:

  `mcaDeltaStar C ε* = 1/4 = (1 − ρ)/2`.

Doubles the landed window `[2/17, 3/17)`; the good side is bands 1–2 verbatim. -/
theorem mcaDeltaStar_C84_eq_quarter_wide {εstar : ℝ≥0∞}
    (hlo : 2/17 ≤ εstar) (hhi : εstar < 6/17) :
    MCAThresholdLedger.mcaDeltaStar (F := F17) (A := F17)
      (C84 : Set (Fin 8 → F17)) εstar = 1/4 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
      (lt_of_lt_of_le hhi epsMCA_quarter_ge_six)) ?_
  by_contra h
  push Not at h
  obtain ⟨c, hc1, hc2⟩ := exists_between h
  have hmem : c ∈ MCAThresholdLedger.mcaGoodRadii (F := F17) (A := F17)
      (C84 : Set (Fin 8 → F17)) εstar := by
    have hq1 : (1/4 : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num : (0:ℝ≥0) < 4)]
      norm_num
    refine ⟨le_of_lt (lt_of_lt_of_le hc2 hq1), ?_⟩
    exact le_trans (epsMCA_le_of_lt_quarter hc2) hlo
  have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good (F := F17) (A := F17)
    (C84 : Set (Fin 8 → F17)) εstar hmem.1 hmem.2
  exact absurd hle (not_le.mpr hc1)

end ProximityGap.DeltaStarSecondPin

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeltaStarSecondPin.epsMCA_quarter_ge_six
#print axioms ProximityGap.DeltaStarSecondPin.mcaDeltaStar_C84_eq_quarter_wide
