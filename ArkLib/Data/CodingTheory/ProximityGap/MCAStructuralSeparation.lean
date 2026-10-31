/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact

/-!
# Zero versus positive MCA error: the two structural extremes (Issues #141 / #171)

This file records, with full proof, a strict **zero-versus-positive** separation of the MCA error
between the two structural extremes:

* **`epsMCA_bot_ge_inv_card_radius`** — the zero code has `ε_mca(⊥, δ) ≥ 1/|F| > 0` at **every**
  radius `δ` (the firing stack `(0, 𝟙)` always fires at `γ = 0`).
* The full code has `ε_mca(univ, δ) = 0` (`epsMCA_univ_eq_zero`, fleet).
* **`epsMCA_univ_lt_epsMCA_bot`** — therefore `ε_mca(univ, δ) < ε_mca(⊥, δ')` strictly, for all
  radii.

**What this does NOT show (audit PG-065).**  The Grand Challenge 1 conjecture asks for a
`poly(n)/q` bound on `ε_mca(C, δ)` for Reed–Solomon codes.  Both examples here *satisfy* such a
bound: the full code has numerator `0`, and the zero code's exact error
(`MCAZeroCodeCharacterization.epsMCA_bot_eq_floor_succ_div`, for `δ ≤ 1` and
`⌊δn⌋+1 ≤ min(n, |F|)`) is `(⌊δn⌋+1)/|F| ≤ (n+1)/q`.
A lower bound `1/q` is entirely compatible with `poly(n)/q` smallness, so these finite
examples do **not** show that `poly(n)/q` smallness "requires code structure" or is a non-automatic
property.  Establishing that would need a code family whose MCA-error numerator exceeds every fixed
polynomial in `n` in the required parameter regime; no such family is exhibited here.  The valid
content is the strict zero-versus-positive separation above.
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
      mul_le_mul_of_nonneg_right tsub_le_self (by positivity)
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

/-- **Strict zero-versus-positive MCA-error separation.** The full code has zero MCA error while
the zero code has error `≥ 1/|F| > 0` at every radius, so `ε_mca(univ, δ) < ε_mca(⊥, δ')` for all
radii `δ, δ'`.  This does NOT separate `poly(n)/q` smallness: both codes satisfy a `poly(n)/q`
bound (numerators `0` and `⌊δn⌋+1 ≤ n+1`), so it gives no evidence that a uniform `poly(n)/q`
bound on `ε_mca` (Grand Challenge 1) fails without code structure (audit PG-065). -/
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
