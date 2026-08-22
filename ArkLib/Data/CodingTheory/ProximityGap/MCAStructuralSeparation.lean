/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact

/-!
# MCA-error smallness is a genuine structural property (Issues #141 / #171)

The Grand Challenge 1 conjecture asks for a `poly(n)/q` bound on `ε_mca(C, δ)` for Reed–Solomon
codes. This file records, with full proof, that such smallness is **not** a formal triviality: it
already separates the two structural extremes.

* **`epsMCA_bot_ge_inv_card_radius`** — the zero code has `ε_mca(⊥, δ) ≥ 1/|F| > 0` at **every**
  radius `δ` (the firing stack `(0, 𝟙)` always fires at `γ = 0`).
* The full code has `ε_mca(univ, δ) = 0` (`epsMCA_univ_eq_zero`, fleet).
* **`epsMCA_univ_lt_epsMCA_bot`** — therefore `ε_mca(univ, δ) < ε_mca(⊥, δ')` strictly, for all
  radii. Any uniform `ε_mca ≤ poly(n)/q` statement must genuinely use the code's structure: the
  zero code already violates "smallness is automatic," and (by the exact characterization in
  `MCAZeroCodeExactRange` and its extension) its error in fact *grows* with `δ` as `⌊δn⌋+1)/|F|`.

This is the honest formal content behind the #171 observation that "smallness needs structure":
the answer-shaped property is real, not vacuous.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

section Separation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`mcaEvent` fires at `γ = 0`** for the stack `ubad`, at *every* radius `δ` (`S = univ`
satisfies `|univ| = |ι| ≥ (1-δ)|ι|`). (Inlined here so this module depends only on
`MCAZeroCodeExact`.) -/
theorem mcaEvent_ubad_anyδ (δ : ℝ≥0) :
    mcaEvent (F := F) (Cbot : Set (ι → F)) δ (ubad 0) (ubad 1) (0 : F) := by
  classical
  refine ⟨Finset.univ, ?_, ⟨0, zero_mem_Cbot, ?_⟩, ?_⟩
  · rw [Finset.card_univ]
    have h : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ 1 * (Fintype.card ι : ℝ≥0) :=
      mul_le_mul_right' tsub_le_self _
    simpa using h
  · intro i _; simp
  · rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hcontra := (hagree i₀ (Finset.mem_univ i₀)).2
    rw [(mem_Cbot_iff v₁).mp hv₁, ubad_one] at hcontra
    simp only [Pi.zero_apply] at hcontra
    exact absurd hcontra zero_ne_one

/-- **The zero code has `ε_mca ≥ 1/|F|` at every radius.** -/
theorem epsMCA_bot_ge_inv_card_radius (δ : ℝ≥0) :
    (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ :=
  epsMCA_ge_inv_card_of_mcaEvent (F := F) (A := F) (Cbot : Set (ι → F)) δ ubad 0
    (mcaEvent_ubad_anyδ δ)

/-- `1/|F| > 0`. -/
theorem inv_card_pos : (0 : ℝ≥0∞) < (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [ENNReal.div_pos_iff]
  exact ⟨one_ne_zero, ENNReal.natCast_ne_top _⟩

/-- **The zero code has strictly positive MCA error at every radius.** -/
theorem epsMCA_bot_pos_radius (δ : ℝ≥0) :
    (0 : ℝ≥0∞) < epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ :=
  lt_of_lt_of_le inv_card_pos (epsMCA_bot_ge_inv_card_radius δ)

/-- **MCA-error smallness requires code structure.** The full code has zero MCA error while the
zero code has error `≥ 1/|F| > 0` at every radius, so `ε_mca(univ, δ) < ε_mca(⊥, δ')` for all
radii `δ, δ'`. Hence a uniform `poly(n)/q` bound on `ε_mca` (Grand Challenge 1) is a genuine
structural property of the code, not an automatic fact. -/
theorem epsMCA_univ_lt_epsMCA_bot (δ δ' : ℝ≥0) :
    epsMCA (F := F) (A := F) (Set.univ : Set (ι → F)) δ
      < epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ' := by
  rw [epsMCA_univ_eq_zero]
  exact epsMCA_bot_pos_radius δ'

end Separation

/-! ## Source audit -/

#print axioms epsMCA_bot_ge_inv_card_radius
#print axioms epsMCA_univ_lt_epsMCA_bot

end ProximityGap.MCAZeroCode
