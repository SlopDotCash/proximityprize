/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeltaStarSecondPinF17
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# The second pin, MAXIMAL: `δ* = 1/4` on `ε* ∈ [2/17, 7/17)` (#357, items 18/25)

The exhaustive band-3 computation (`probe_band3_exact_value.py`) gives
`ε_mca(C84, 1/4) = 7/17` exactly, attained at the **far-coset** stack
`w₀ = (0,0,0,0,2,0,1,0)`, `w₁ = (0,0,0,0,1,0,1,16)` with seven bad scalars
`γ ∈ {0, 4, 7, 8, 10, 15, 16}`.  This file formalizes the lower bound and the
resulting maximal pin window:

* `w₁_far` — the far-coset condition: **no codeword agrees with `w₁` on six
  positions**.  Proof: a codeword agreeing on ≥ 4 of `w₁`'s five zero positions is
  zero (root counting) and then fails at a support point; otherwise it agrees on all
  three supports and exactly three zeros, hence equals the explicit support-cubic
  through its first agreed zero `z₁ ∈ {0,1,2}` (such a `z₁` exists: the exceptional
  pair `{3,5}` has only two elements) — and that cubic vanishes at no other zero
  point (four explicit evaluations).
* seven certificates via `mcaEvent_iff_line_explainable` — the far-coset law makes
  the no-joint side automatic; each certificate is a pure line explanation.
* `mcaDeltaStar_C84_eq_quarter_maximal` — `δ* = 1/4` on `ε* ∈ [2/17, 7/17)`,
  the **maximal** window (the band value is exactly `7/17`).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.FarCosetExplosion

namespace ProximityGap.DeltaStarSecondPin

/-! ## The extremal far-coset stack -/

/-- The first row of the extremal band-3 stack. -/
def w₀ : Fin 8 → F17 := ![0, 0, 0, 0, 2, 0, 1, 0]

/-- The second row: a coset of minimum weight `3` — the far-coset side of the
explosion dichotomy. -/
def w₁ : Fin 8 → F17 := ![0, 0, 0, 0, 1, 0, 1, 16]

/-- Uniqueness through four points: two codewords agreeing at four domain points
are equal. -/
theorem codeword_eq_of_agree_four {c c' : Fin 8 → F17} (hc : c ∈ C84) (hc' : c' ∈ C84)
    (i1 i2 i3 i4 : Fin 8)
    (hcard : ({dom i1, dom i2, dom i3, dom i4} : Finset F17).card = 4)
    (h1 : c i1 = c' i1) (h2 : c i2 = c' i2) (h3 : c i3 = c' i3) (h4 : c i4 = c' i4) :
    c = c' := by
  have hsub : c - c' = 0 := by
    refine codeword_eq_zero_of_vanishing (c - c') (C84.sub_mem hc hc')
      {dom i1, dom i2, dom i3, dom i4} (le_of_eq hcard.symm) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨i1, rfl, by simp [h1]⟩
    · exact ⟨i2, rfl, by simp [h2]⟩
    · exact ⟨i3, rfl, by simp [h3]⟩
    · exact ⟨i4, rfl, by simp [h4]⟩
  have := congrFun hsub
  funext i
  have hi := this i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
  exact hi

/-- The support cubic through zero position `z₁`: agreeing with `w₁` at the three
supports `{4,6,7}` and vanishing at `dom z₁`, for `z₁ ∈ {0,1,2}` the cubic vanishes
at NO other zero position of `w₁`. -/
def suppCubic : Fin 8 → (Fin 8 → F17)
  | 0 => fun i => 12 + 10 * dom i + 14 * dom i ^ 2 + 15 * dom i ^ 3
  | 1 => fun i => 6 + 6 * dom i + 2 * dom i ^ 2 + 1 * dom i ^ 3
  | 2 => fun i => 1 + 14 * dom i + 9 * dom i ^ 2 + 12 * dom i ^ 3
  | _ => 0

/-- **The far-coset condition for `w₁`**: no codeword agrees with it on any
six positions. -/
theorem w₁_far : FarFromCode (C84 : Set (Fin 8 → F17)) (1/4) w₁ := by
  intro c hc S hS
  by_contra h
  push Not at h
  -- size: 6 ≤ |S|
  have h14 : (1/4 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0:ℝ≥0) < 4)]
    norm_num
  have h34 : (1 : ℝ≥0) - 1/4 = 3/4 := by
    rw [tsub_eq_iff_eq_add_of_le h14, ← NNReal.coe_inj]
    push_cast
    norm_num
  have hcard : 6 ≤ S.card := by
    have := hS
    rw [h34, Fintype.card_fin] at this
    have h6 : (6 : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      calc (6 : ℝ≥0) = 3/4 * 8 := by norm_num
        _ ≤ (S.card : ℝ≥0) := this
    exact_mod_cast h6
  -- split S into zero and support positions of w₁
  classical
  set Z : Finset (Fin 8) := S.filter (fun i => w₁ i = 0) with hZ
  set P : Finset (Fin 8) := S.filter (fun i => ¬ w₁ i = 0) with hP
  have hZP : Z.card + P.card = S.card := Finset.filter_card_add_filter_neg_card_eq_card _
  have hPsub : P ⊆ ({4, 6, 7} : Finset (Fin 8)) := by
    intro i hi
    have hiw := (Finset.mem_filter.mp hi).2
    fin_cases i <;> revert hiw <;> decide
  have hPcard : P.card ≤ 3 := le_trans (Finset.card_le_card hPsub) (by decide)
  have hZ3 : 3 ≤ Z.card := by omega
  by_cases h4 : 4 ≤ Z.card
  · -- c vanishes at ≥ 4 domain points ⟹ c = 0 ⟹ fails at a support point of S
    have hc0 : c = 0 := by
      refine codeword_eq_zero_of_vanishing c hc (Z.image dom) ?_ ?_
      · rw [Finset.card_image_of_injective _ dom_injective]
        exact h4
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        refine ⟨i, rfl, ?_⟩
        rw [h i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2]
    have hPne : P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hPe
      have hSZ : S.card ≤ 5 := by
        have hZsub : Z ⊆ ({0, 1, 2, 3, 5} : Finset (Fin 8)) := by
          intro i hi
          have hiw := (Finset.mem_filter.mp hi).2
          fin_cases i <;> revert hiw <;> decide
        have : Z.card ≤ 5 := le_trans (Finset.card_le_card hZsub) (by decide)
        have hPc : P.card = 0 := by rw [hPe]; rfl
        omega
      omega
    obtain ⟨i, hi⟩ := hPne
    have hiS := (Finset.mem_filter.mp hi).1
    have hiw := (Finset.mem_filter.mp hi).2
    have := h i hiS
    rw [hc0] at this
    exact hiw (by simpa using this.symm)
  · -- |Z| = 3: all three supports in S, three zeros; route through z₁ ∈ {0,1,2}
    have hZc : Z.card = 3 := by omega
    have hPc : P.card = 3 := by omega
    have hPeq : P = ({4, 6, 7} : Finset (Fin 8)) :=
      Finset.eq_of_subset_of_card_le hPsub (by rw [hPc]; decide)
    -- supports are in S with the right values
    have hmem : ∀ i ∈ ({4, 6, 7} : Finset (Fin 8)), c i = w₁ i := by
      intro i hi
      have : i ∈ P := by rw [hPeq]; exact hi
      exact h i (Finset.mem_filter.mp this).1
    have hc4 : c 4 = 1 := by have := hmem 4 (by decide); simpa [w₁] using this
    have hc6 : c 6 = 1 := by have := hmem 6 (by decide); simpa [w₁] using this
    have hc7 : c 7 = 16 := by have := hmem 7 (by decide); simpa [w₁] using this
    -- a zero of S in {0,1,2}: Z ⊆ {0,1,2,3,5} with |Z| = 3 > |{3,5}|
    have hZsub : Z ⊆ ({0, 1, 2, 3, 5} : Finset (Fin 8)) := by
      intro i hi
      have hiw := (Finset.mem_filter.mp hi).2
      fin_cases i <;> revert hiw <;> decide
    have hz1 : ∃ z₁ ∈ Z, z₁ ∈ ({0, 1, 2} : Finset (Fin 8)) := by
      by_contra hno
      push Not at hno
      have hZ35 : Z ⊆ ({3, 5} : Finset (Fin 8)) := by
        intro i hi
        have h5 := hZsub hi
        have h3 := hno i hi
        revert h5 h3
        fin_cases i <;> decide
      have h35 : Z.card ≤ 2 := le_trans (Finset.card_le_card hZ35) (by decide)
      omega
    obtain ⟨z₁, hz₁Z, hz₁012⟩ := hz1
    -- c equals the explicit support cubic through z₁
    have hz₁S := (Finset.mem_filter.mp hz₁Z).1
    have hz₁0 : c z₁ = 0 := by
      have := h z₁ hz₁S
      rw [this, (Finset.mem_filter.mp hz₁Z).2]
    -- pick a second zero z₂ ≠ z₁
    have hz2 : ∃ z₂ ∈ Z, z₂ ≠ z₁ := by
      have h1 : (Z.erase z₁).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hz₁Z]
        omega
      obtain ⟨z₂, hz₂e⟩ := h1
      exact ⟨z₂, Finset.mem_of_mem_erase hz₂e, Finset.ne_of_mem_erase hz₂e⟩
    obtain ⟨z₂, hz₂Z, hz₂ne⟩ := hz2
    have hz₂S := (Finset.mem_filter.mp hz₂Z).1
    have hz₂0 : c z₂ = 0 := by
      have := h z₂ hz₂S
      rw [this, (Finset.mem_filter.mp hz₂Z).2]
    have hz₂sub := hZsub hz₂Z
    -- the kill: c = suppCubic z₁ by 4-point uniqueness; evaluate at z₂
    fin_cases hz₁012
    -- z₁ = 0: cubic [12,10,14,15]
    · have hcub : (suppCubic 0) ∈ C84 := cubic_mem (12 : F17) 10 14 15
      have hceq : c = suppCubic 0 :=
        codeword_eq_of_agree_four hc hcub 4 6 7 0 (by decide)
          (by rw [hc4]; decide) (by rw [hc6]; decide) (by rw [hc7]; decide)
          (by rw [hz₁0]; decide)
      rw [hceq] at hz₂0
      fin_cases hz₂sub <;> revert hz₂0 <;> first
        | (intro hz₂0; exact absurd hz₂0 (by decide))
        | (intro _; exact hz₂ne rfl)
    -- z₁ = 1: cubic [6,6,2,1]
    · have hcub : (suppCubic 1) ∈ C84 := cubic_mem (6 : F17) 6 2 1
      have hceq : c = suppCubic 1 :=
        codeword_eq_of_agree_four hc hcub 4 6 7 1 (by decide)
          (by rw [hc4]; decide) (by rw [hc6]; decide) (by rw [hc7]; decide)
          (by rw [hz₁0]; decide)
      rw [hceq] at hz₂0
      fin_cases hz₂sub <;> revert hz₂0 <;> first
        | (intro hz₂0; exact absurd hz₂0 (by decide))
        | (intro _; exact hz₂ne rfl)
    -- z₁ = 2: cubic [1,14,9,12]
    · have hcub : (suppCubic 2) ∈ C84 := cubic_mem (1 : F17) 14 9 12
      have hceq : c = suppCubic 2 :=
        codeword_eq_of_agree_four hc hcub 4 6 7 2 (by decide)
          (by rw [hc4]; decide) (by rw [hc6]; decide) (by rw [hc7]; decide)
          (by rw [hz₁0]; decide)
      rw [hceq] at hz₂0
      fin_cases hz₂sub <;> revert hz₂0 <;> first
        | (intro hz₂0; exact absurd hz₂0 (by decide))
        | (intro _; exact hz₂ne rfl)

/-! ## The seven certificates (far-coset law: line explanation suffices) -/

/-- Certificate engine: a line explanation alone certifies badness for the far
stack. -/
theorem wcert (γ : F17) (T : Finset (Fin 8)) (hT : T.card = 6)
    (w : Fin 8 → F17) (hw : w ∈ C84)
    (hag : ∀ i ∈ T, w i = w₀ i + γ • w₁ i) :
    mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ γ := by
  rw [mcaEvent_iff_line_explainable (C84 : Set (Fin 8 → F17)) (1/4) w₁_far γ]
  exact ⟨T, card_clause hT, w, hw, hag⟩

theorem wcert0 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 0 := by
  refine wcert 0 {0, 1, 2, 3, 5, 7} (by decide) 0 C84.zero_mem ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert4 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 4 := by
  refine wcert 4 {2, 3, 4, 5, 6, 7} (by decide) _ (cubic_mem 4 9 10 16) ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert7 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 7 := by
  refine wcert 7 {0, 3, 4, 5, 6, 7} (by decide) _ (cubic_mem 8 12 5 9) ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert8 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 8 := by
  refine wcert 8 {1, 3, 4, 5, 6, 7} (by decide) _ (cubic_mem 15 13 9 1) ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert10 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 10 := by
  refine wcert 10 {0, 1, 2, 4, 6, 7} (by decide) _ (cubic_mem 10 8 13 3) ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert15 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 15 := by
  refine wcert 15 {0, 1, 2, 3, 4, 5} (by decide) 0 C84.zero_mem ?_
  intro i hi
  fin_cases hi <;> decide

theorem wcert16 : mcaEvent (F := F17) (C84 : Set (Fin 8 → F17)) (1/4) w₀ w₁ 16 := by
  refine wcert 16 {0, 1, 2, 3, 5, 6} (by decide) 0 C84.zero_mem ?_
  intro i hi
  fin_cases hi <;> decide

/-- **Bad side, maximal:** `ε_mca(C84, 1/4) ≥ 7/17`. -/
theorem epsMCA_quarter_ge_seven :
    (7 / 17 : ℝ≥0∞) ≤ epsMCA (F := F17) (A := F17) (C84 : Set (Fin 8 → F17)) (1/4) := by
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (C84 : Set (Fin 8 → F17)) (1/4) ![w₀, w₁]
    ({0, 4, 7, 8, 10, 15, 16} : Finset F17) ?_
  · have hcard : ({0, 4, 7, 8, 10, 15, 16} : Finset F17).card = 7 := by decide
    have hF : (Fintype.card F17 : ℝ≥0∞) = 17 := by
      rw [show Fintype.card F17 = 17 from by simp [ZMod.card]]
      norm_num
    rwa [hcard, hF] at h
  · intro γ hγ
    fin_cases hγ
    · simpa using wcert0
    · simpa using wcert4
    · simpa using wcert7
    · simpa using wcert8
    · simpa using wcert10
    · simpa using wcert15
    · simpa using wcert16

/-! ## The maximal pin -/

/-- **THE SECOND PIN, MAXIMAL.**  For `C = RS[F₁₇, ⟨2⟩, 4]` and every
`ε* ∈ [2/17, 7/17)`:  `mcaDeltaStar C ε* = 1/4`.  The window is maximal: the
exhaustive band-3 computation gives `ε_mca(C84, 1/4) = 7/17` exactly. -/
theorem mcaDeltaStar_C84_eq_quarter_maximal {εstar : ℝ≥0∞}
    (hlo : 2/17 ≤ εstar) (hhi : εstar < 7/17) :
    MCAThresholdLedger.mcaDeltaStar (F := F17) (A := F17)
      (C84 : Set (Fin 8 → F17)) εstar = 1/4 := by
  refine le_antisymm
    (MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
      (lt_of_lt_of_le hhi epsMCA_quarter_ge_seven)) ?_
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
#print axioms ProximityGap.DeltaStarSecondPin.w₁_far
#print axioms ProximityGap.DeltaStarSecondPin.epsMCA_quarter_ge_seven
#print axioms ProximityGap.DeltaStarSecondPin.mcaDeltaStar_C84_eq_quarter_maximal
