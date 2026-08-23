/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonNumericBridge

/-!
# The unconditional bad-scalar count on the unique-decoding window

Depth-0 end-to-end capstone of the #302 capture-kernel chain: on the 3-intersection
window `2n + k ≤ 3·⌈(1−δ)n⌉`, the bad-scalar set of **every** word stack has at most `n`
members, with **no hypotheses left** — the global decode family exists by choice
(`exists_mcaDecode_of_mcaEvent`), and `cell_card_le_of_decode_family_window` (K4 at
depth 0 + the proven Claim-1 dichotomy) bounds the whole set as a single cell.

* `badScalars_card_le_of_window` — `#badScalars(u) ≤ n` for every stack `u`;
* `johnsonNumericBound_of_window` — hence the `JohnsonNumericBound` residual holds
  outright on the window, given only the numeric comparison `n/|F| ≤ johnsonBoundReal`.

This is the first regime where the Johnson MCA chain closes unconditionally; beyond the
window, the same two inputs are produced by `GSCellProduction.lean` (K1 + factor surface)
and await K4 past unique decoding (BCIKS20 Steps 5–7).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Finset
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **The unconditional bad-scalar count on the unique-decoding window**: every word
stack has at most `n` bad scalars. The whole bad set is one decoded cell (decode family
by choice), and depth-0 K4 + the Claim-1 dichotomy bound it. -/
theorem badScalars_card_le_of_window (domain : ι₀ ↪ F₀) {k : ℕ} (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀) (hk : 0 < k)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    (Finset.univ.filter (fun γ : F₀ =>
      _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀)))
        δ (u 0) (u 1) γ)).card ≤ Fintype.card ι₀ := by
  classical
  set bad : Finset F₀ := Finset.univ.filter (fun γ : F₀ =>
    _root_.ProximityGap.mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀)))
      δ (u 0) (u 1) γ) with hbad
  have hex : ∀ γ : F₀, ∃ p : F₀[X],
      γ ∈ bad → ∃ d : McaDecode domain k δ u γ, d.P = p := by
    intro γ
    by_cases hγ : γ ∈ bad
    · obtain ⟨d⟩ := exists_mcaDecode_of_mcaEvent (Finset.mem_filter.mp hγ).2
      exact ⟨d.P, fun _ => ⟨d, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hγ⟩
  choose P hPdec using hex
  exact cell_card_le_of_decode_family_window hk bad (Fintype.card ι₀) P le_rfl
    (fun γ hγ => hPdec γ hγ) hwin

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **The `JohnsonNumericBound` residual holds outright on the window**: the uniform
count `n` from `badScalars_card_le_of_window`, fed through the S11 counting seam, leaves
only the numeric comparison `n / |F| ≤ johnsonBoundReal`. -/
theorem johnsonNumericBound_of_window (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hk : 0 < k)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊)
    (hNdiv : (Fintype.card ι₀ : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ :=
  JohnsonNumericBound.of_card_le_nat domain k η δ (Fintype.card ι₀) hNdiv
    (fun u => badScalars_card_le_of_window domain δ u hk hwin)

/-- The Hab25 `ℓ`-budget is at least `1` whenever `k + 1 ≤ n`: `ρ₊ ≤ 1` makes the
denominator `3·ρ₊^{3/2} ≤ 3`, while `m ≥ 3` makes the numerator `2(m+½)⁵ ≥ 1050`. -/
lemma hab25_ell_budget_ge_one {n k : ℕ} (hn : 0 < n) (hkn : k + 1 ≤ n) (η : ℝ≥0) :
    (1 : ℝ) ≤ 2 * (hab25M n k η + 1 / 2) ^ 5 /
      (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  have hρpos := hab25RhoPlus_pos hn k
  have hρ1 : hab25RhoPlus n k ≤ 1 := by
    rw [hab25RhoPlus, ← add_div, div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hkn
  have hρ32 : hab25RhoPlus n k ^ ((3 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one hρpos.le hρ1 (by norm_num)
  have hρ32pos : (0 : ℝ) < hab25RhoPlus n k ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hρpos _
  have hm := hab25M_ge_three n k η
  have hm5 : ((7 : ℝ) / 2) ^ 5 ≤ (hab25M n k η + 1 / 2) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 5
  rw [le_div_iff₀ (by positivity)]
  nlinarith

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **The numeric comparison holds outright**: `n / |F| ≤ johnsonBoundReal` whenever
`k + 1 ≤ n` — the `L = 1` case of the closed-form numeric edge. -/
theorem card_div_le_johnsonBoundReal (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hkn : k + 1 ≤ Fintype.card ι₀) :
    (Fintype.card ι₀ : ℝ) / (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ := by
  have h := nat_mul_card_div_le_johnsonBoundReal domain k η δ 1
    (by simpa using hab25_ell_budget_ge_one Fintype.card_pos hkn η)
  simpa using h

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **The `JohnsonNumericBound` residual, fully discharged on the window**: only the
window inequality and `k + 1 ≤ n` remain — no numeric side condition. -/
theorem johnsonNumericBound_of_window' (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hk : 0 < k) (hkn : k + 1 ≤ Fintype.card ι₀)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_window domain k η δ hk hwin
    (card_div_le_johnsonBoundReal domain k η δ hkn)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badScalars_card_le_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25_ell_budget_ge_one
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.card_div_le_johnsonBoundReal
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_window'
