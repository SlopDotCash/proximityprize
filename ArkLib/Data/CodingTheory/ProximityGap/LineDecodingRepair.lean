/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingRefutation

/-!
# Repair scaffolding for the refuted ABF26 Theorem 4.21 (issue #140)

The black-box `lineDecodable_imp_epsMCA_le_target` is proven **false** in `LineDecodingRefutation`
(the `Czero = ⊥`, `δ = a = 0` counterexample). This module records honest, axiom-clean *repair*
progress that does NOT require the (absent) Guruswami–Sudan interpolation core:

* **(A) Counterexample-exclusion.**
  `refutation_tuple_excluded` proves the in-tree refuting tuple satisfies `LineDecodable` but fails
  the nondegeneracy conjunction (`C ≠ ⊥` and `0 < a`).

* **(B) Exact value `ε_mca(Czero, 0) = 1/|F|`.** `epsMCA_Czero_eq_inv_card` sharpens the in-tree
  bare `0 < ε_mca` to the precise gap (`= 1/2` over `ZMod 2`), via the structural fact that the
  zero code's `mcaEvent` cannot fire at two distinct scalars (`not_mcaEvent_both`). This pins the
  refutation gap and shows any repair needs `1 ≤ a` — the quantitative form of the `0 < a` repair.
-/

namespace CodingTheory.LineDecodingRepair

open scoped NNReal ProbabilityTheory ENNReal
open CodingTheory ProximityGap Code
open CodingTheory.LineDecodingRefutation

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## (A) Strengthened statement + counterexample-exclusion -/



/-- The in-tree refutation code `Czero` is definitionally the zero submodule. -/
theorem Czero_eq_bot : (Czero : ModuleCode ι F A) = ⊥ := rfl

/-- **The refutation data violates the `C ≠ ⊥` hypothesis**, so the refutation cannot be re-run
against `lineDecodable_imp_epsMCA_le_nondegenerate`. -/
theorem Czero_violates_nondegeneracy : ¬ ((Czero : ModuleCode ι F A) ≠ ⊥) := by
  simp [Czero_eq_bot]

/-- **The refutation data also violates `0 < a`** (it uses `a = 0`). -/
theorem Czero_a_violates_pos : ¬ ((0 : ℝ≥0) > 0) := by simp

/-- **The repaired statement's hypotheses are jointly unsatisfiable by the exact refuting tuple**
`(Czero, δ = 0, a = 0)`: it satisfies `LineDecodable` (`lineDecodable_Czero`) yet fails
`C ≠ ⊥ ∧ 0 < a`. The known refutation is excluded by the repair. -/
theorem refutation_tuple_excluded :
    LineDecodable (F := F) ((Czero : Set (ι → A))) 0 0 ((Fintype.card ι : ℝ≥0) + 1)
      ∧ ¬ ((Czero : ModuleCode ι F A) ≠ ⊥ ∧ (0 : ℝ≥0) > 0) :=
  ⟨lineDecodable_Czero 0 0, fun ⟨hC, _⟩ => hC Czero_eq_bot⟩

/-! ## (B) Exact value `ε_mca(Czero, 0) = 1/|F|`, via the no-two-scalars structure -/

/-- **Structural core for the zero code.** If `mcaEvent` fires for the zero code at scalar `γ`, the
affine value at the unique coordinate vanishes and the stack is non-trivial there. -/
theorem mcaEvent_Czero_pos0 {u₀ u₁ : ι → A} {γ : F}
    (h : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ) :
    (u₀ 0 + γ • u₁ 0 = 0) ∧ (u₀ 0 ≠ 0 ∨ u₁ 0 ≠ 0) := by
  classical
  obtain ⟨S, hScard, ⟨w, hw, hwline⟩, hno⟩ := h
  have hw0 : w = 0 := (mem_Czero_iff w).mp hw
  rw [show (Fintype.card ι : ℕ) = 1 from by decide] at hScard
  have hcard1 : (1 : ℝ≥0) ≤ (S.card : ℝ≥0) := by simpa using hScard
  have hcardNat : 1 ≤ S.card := by exact_mod_cast hcard1
  have h0 : (0 : ι) ∈ S := by
    rcases Finset.card_pos.mp (by omega : 0 < S.card) with ⟨x, hx⟩
    have : x = 0 := Subsingleton.elim x 0
    rwa [this] at hx
  have hlin : u₀ 0 + γ • u₁ 0 = 0 := by
    have := hwline 0 h0; rw [hw0] at this; simpa using this.symm
  refine ⟨hlin, ?_⟩
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hu0, hu1⟩ := hcon
  apply hno
  refine ⟨0, Czero.zero_mem, 0, Czero.zero_mem, ?_⟩
  intro i hi
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  exact ⟨by simp [hu0], by simp [hu1]⟩

/-- **The zero code's `mcaEvent` cannot fire at two distinct scalars** (`0` and `1` over `ZMod 2`):
the "single shared miss" obstruction realised as a clean impossibility. -/
theorem not_mcaEvent_both {u₀ u₁ : ι → A}
    (h0 : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ (0 : F))
    (h1 : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ (1 : F)) : False := by
  obtain ⟨hlin0, _⟩ := mcaEvent_Czero_pos0 h0
  obtain ⟨hlin1, hne1⟩ := mcaEvent_Czero_pos0 h1
  simp only [zero_smul, add_zero] at hlin0
  simp only [one_smul, hlin0, zero_add] at hlin1
  rcases hne1 with h | h
  · exact h hlin0
  · exact h hlin1

/-- **Per-stack upper bound: every stack's `mcaEvent` probability for the zero code is `≤ 1/|F|`.** -/
theorem mcaProb_Czero_le_half (u : WordStack A (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) γ]
      ≤ (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator, tsum_fintype]
  have hcardF : ((Fintype.card F : ℕ) : ENNReal) = (2 : ENNReal) := by
    rw [show (Fintype.card F : ℕ) = 2 from by decide]; rfl
  have hw : ∀ γ : F, ($ᵖ F) γ = (1 : ENNReal) / 2 := by
    intro γ; rw [PMF.uniformOfFintype_apply, hcardF, one_div]
  have huniv : (Finset.univ : Finset F) = {0, 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hw]
  rw [hcardF]
  by_cases hb0 : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) (0 : F)
  · have hnb1 : ¬ mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) (1 : F) :=
      fun h1 => not_mcaEvent_both hb0 h1
    rw [if_neg hnb1, mul_zero, add_zero, if_pos hb0, mul_one]
  · rw [if_neg hb0, mul_zero, zero_add]
    by_cases hb1 : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) (1 : F)
    · rw [if_pos hb1, mul_one]
    · rw [if_neg hb1, mul_zero]; exact zero_le _

/-- **Sharp lower bound `1/|F| ≤ ε_mca(Czero, 0)`** (sharper than the in-tree `0 < ε_mca`). -/
theorem epsMCA_Czero_ge_half :
    (1 : ENNReal) / (Fintype.card F : ENNReal)
      ≤ epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) := by
  classical
  have hpoint :
      (1 : ENNReal) / (Fintype.card F : ENNReal) ≤
        Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
          (ubad 0) (ubad 1) γ] := by
    rw [ProbabilityTheory.Pr_eq_tsum_indicator]
    refine le_trans ?_ (ENNReal.le_tsum (0 : F))
    rw [if_pos mcaEvent_ubad_zero, mul_one, PMF.uniformOfFintype_apply, one_div]
  refine le_trans hpoint ?_
  unfold epsMCA
  exact le_iSup (fun u : WordStack A (Fin 2) ι =>
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) γ]) ubad

/-- **Upper bound `ε_mca(Czero, 0) ≤ 1/|F|`** from the per-stack bound via `iSup_le`. -/
theorem epsMCA_Czero_le_half :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      ≤ (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold epsMCA
  exact iSup_le mcaProb_Czero_le_half

/-- **Exact value: `ε_mca(Czero, 0) = 1/|F|`.** Sharpens the in-tree `epsMCA_Czero_pos` (`0 < ε_mca`)
to the precise gap: the repaired conclusion `ε_mca ≤ a/|F|` fails at `a = 0` by exactly `1/|F|`, so
any repair needs `1 ≤ a` — the `0 < a` nondegeneracy made quantitative. -/
theorem epsMCA_Czero_eq_inv_card :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      = (1 : ENNReal) / (Fintype.card F : ENNReal) :=
  le_antisymm epsMCA_Czero_le_half epsMCA_Czero_ge_half

/-- Numeric specialisation over `F = ZMod 2`: `ε_mca(Czero, 0) = 1/2`. -/
theorem epsMCA_Czero_eq_half :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) = (1 : ENNReal) / 2 := by
  rw [epsMCA_Czero_eq_inv_card]
  have : ((Fintype.card F : ℕ) : ENNReal) = (2 : ENNReal) := by
    rw [show (Fintype.card F : ℕ) = 2 from by decide]; rfl
  rw [this]

end CodingTheory.LineDecodingRepair

#print axioms CodingTheory.LineDecodingRepair.refutation_tuple_excluded

#print axioms CodingTheory.LineDecodingRepair.epsMCA_Czero_eq_inv_card
#print axioms CodingTheory.LineDecodingRepair.not_mcaEvent_both
