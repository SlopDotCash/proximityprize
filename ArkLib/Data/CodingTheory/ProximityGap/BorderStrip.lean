/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Border strips: the no-2×2 condition as a row-length inequality (#389)

A skew shape `λ/μ` is a **border strip** (rim hook) when it is connected and contains no `2×2`
box. This file formalizes the `2×2`-free half geometrically and reduces it to a clean condition on
row lengths — no Maya-diagram ↔ cell correspondence required:

> **`has2x2_iff_rowLen`** — `λ/μ` contains a `2×2` box **iff** `∃ i, μ.rowLen i + 1 < λ.rowLen (i+1)`.
> Equivalently (`no2x2_iff_rowLen`), it is `2×2`-free iff `∀ i, λ.rowLen (i+1) ≤ μ.rowLen i + 1`.

This is the geometric content of "border strip" expressed entirely through row lengths, the form
in which the abacus bead-move (rim-hook removal) is naturally analyzed.
-/

open YoungDiagram

namespace ArkLib.ProximityGap.BorderStrip

variable {μ ν : YoungDiagram}

/-- The skew shape `ν/μ` contains a `2×2` box: four cells of `ν`, none in `μ`. -/
def Has2x2 (μ ν : YoungDiagram) : Prop :=
  ∃ i j, ((i, j) ∈ ν ∧ (i, j) ∉ μ) ∧ ((i, j + 1) ∈ ν ∧ (i, j + 1) ∉ μ) ∧
    ((i + 1, j) ∈ ν ∧ (i + 1, j) ∉ μ) ∧ ((i + 1, j + 1) ∈ ν ∧ (i + 1, j + 1) ∉ μ)

/-- Row lengths grow under `≤` of Young diagrams. -/
theorem rowLen_le_of_le (hμν : μ ≤ ν) (i : ℕ) : μ.rowLen i ≤ ν.rowLen i := by
  by_contra hc
  push_neg at hc
  have hmem : (i, ν.rowLen i) ∈ μ := mem_iff_lt_rowLen.mpr hc
  have hmem2 : (i, ν.rowLen i) ∈ ν := hμν hmem
  rw [mem_iff_lt_rowLen] at hmem2
  omega

/-- **The `2×2` box criterion in terms of row lengths.** -/
theorem has2x2_iff_rowLen (hμν : μ ≤ ν) :
    Has2x2 μ ν ↔ ∃ i, μ.rowLen i + 1 < ν.rowLen (i + 1) := by
  constructor
  · rintro ⟨i, j, ⟨_, hij_notμ⟩, _, _, ⟨hij11_ν, _⟩⟩
    refine ⟨i, ?_⟩
    rw [mem_iff_lt_rowLen] at hij11_ν
    rw [mem_iff_lt_rowLen] at hij_notμ
    push_neg at hij_notμ
    omega
  · rintro ⟨i, hi⟩
    refine ⟨i, μ.rowLen i, ?_, ?_, ?_, ?_⟩
    · refine ⟨mem_iff_lt_rowLen.mpr ?_, ?_⟩
      · have h1 : ν.rowLen (i + 1) ≤ ν.rowLen i := ν.rowLen_anti i (i + 1) (by omega)
        omega
      · rw [mem_iff_lt_rowLen]; omega
    · refine ⟨mem_iff_lt_rowLen.mpr ?_, ?_⟩
      · have h1 : ν.rowLen (i + 1) ≤ ν.rowLen i := ν.rowLen_anti i (i + 1) (by omega)
        omega
      · rw [mem_iff_lt_rowLen]; omega
    · refine ⟨mem_iff_lt_rowLen.mpr (by omega), ?_⟩
      · rw [mem_iff_lt_rowLen]
        have h1 : μ.rowLen (i + 1) ≤ μ.rowLen i := μ.rowLen_anti i (i + 1) (by omega)
        omega
    · refine ⟨mem_iff_lt_rowLen.mpr (by omega), ?_⟩
      · rw [mem_iff_lt_rowLen]
        have h1 : μ.rowLen (i + 1) ≤ μ.rowLen i := μ.rowLen_anti i (i + 1) (by omega)
        omega

/-- **The `2×2`-free (border-strip) criterion in terms of row lengths.** -/
theorem no2x2_iff_rowLen (hμν : μ ≤ ν) :
    ¬ Has2x2 μ ν ↔ ∀ i, ν.rowLen (i + 1) ≤ μ.rowLen i + 1 := by
  rw [has2x2_iff_rowLen hμν]
  push_neg
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

end ArkLib.ProximityGap.BorderStrip
