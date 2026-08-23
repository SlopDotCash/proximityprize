/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic

/-!
# Hab25 §3 — the list-size shape fits the Johnson budget

`Hab25JohnsonArithmetic.lean` discharges the closed-form numeric edge for capture lists
within the *quintic budget* `L ≤ 2(m+½)⁵/(3ρ₊^{3/2})`. The GS machinery, however, delivers
list sizes in the **`ℓ`-shape** `L ≤ (m+½)/√ρ₊` (the paper's `D_Y < ℓ` bound). This file
bridges the two:

* `hab25RhoPlus_le_two` — `ρ₊ ≤ 2` whenever `k ≤ n`;
* `johnson_key_arith` — the heart: `3·ρ₊ ≤ 2·(m+½)⁴` (with `ρ₊ ≤ 2`, `m ≥ 3` this is
  `6 ≤ 2·3.5⁴ = 300.125`, true with two orders of magnitude to spare);
* `list_shape_le_budget` — hence `(m+½)/√ρ₊ ≤ 2(m+½)⁵/(3ρ₊^{3/2})`: the `ℓ`-shape list
  bound sits inside the quintic budget;
* `johnsonNumericBound_of_affine_capture_of_list_shape` — the composition: per-stack
  capture lists of size `≤ L` with `L` in the natural `ℓ`-shape discharge the numeric
  residual outright (for `k ≤ n`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

theorem hab25RhoPlus_le_two {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    hab25RhoPlus n k ≤ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have h1 : (k : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn']; exact hk'
  have h2 : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn']; exact hn1
  rw [hab25RhoPlus]
  linarith

/-- **The key arithmetic**: `3·ρ₊ ≤ 2·(m+½)⁴` — with `ρ₊ ≤ 2` and `m ≥ 3` this is
`6 ≤ 2·(3.5)⁴`, true with two orders of magnitude to spare. -/
theorem johnson_key_arith {n k : ℕ} (η : ℝ≥0) (hn : 0 < n) (hk : k ≤ n) :
    3 * hab25RhoPlus n k ≤ 2 * (hab25M n k η + 1 / 2) ^ 4 := by
  have h2 := hab25RhoPlus_le_two hn hk
  have hm := hab25M_ge_three n k η
  nlinarith [sq_nonneg (hab25M n k η + 1 / 2), sq_nonneg (hab25M n k η - 3)]

/-- **The `ℓ`-shape list bound sits inside the quintic budget**:
`(m+½)/√ρ₊ ≤ 2(m+½)⁵/(3ρ₊^{3/2})` for `k ≤ n`. This converts the GS list-size shape
(`D_Y < ℓ = (m+½)/√ρ₊`) into the hypothesis of
`nat_mul_card_div_le_johnsonBoundReal`. -/
theorem list_shape_le_budget {n k : ℕ} (η : ℝ≥0) (hn : 0 < n) (hk : k ≤ n) :
    (hab25M n k η + 1 / 2) / hab25RhoPlus n k ^ ((1 : ℝ) / 2) ≤
      2 * (hab25M n k η + 1 / 2) ^ 5 / (3 * hab25RhoPlus n k ^ ((3 : ℝ) / 2)) := by
  set m : ℝ := hab25M n k η with hm_def
  set ρ : ℝ := hab25RhoPlus n k with hρ_def
  have hρ_pos : 0 < ρ := hab25RhoPlus_pos hn k
  have hm3 : (3 : ℝ) ≤ m := hab25M_ge_three n k η
  have hmhalf : (0 : ℝ) < m + 1 / 2 := by linarith
  have hsqrt_pos : (0 : ℝ) < ρ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hρ_pos _
  have hsplit : ρ ^ ((3 : ℝ) / 2) = ρ * ρ ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_one_add' hρ_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  rw [div_le_div_iff₀ hsqrt_pos (by positivity)]
  rw [hsplit]
  have hka := johnson_key_arith (n := n) (k := k) η hn hk
  rw [← hρ_def, ← hm_def] at hka
  calc (m + 1 / 2) * (3 * (ρ * ρ ^ ((1 : ℝ) / 2)))
      = ((3 * ρ) * (m + 1 / 2)) * ρ ^ ((1 : ℝ) / 2) := by ring
    _ ≤ ((2 * (m + 1 / 2) ^ 4) * (m + 1 / 2)) * ρ ^ ((1 : ℝ) / 2) := by
        have h1 : (3 * ρ) * (m + 1 / 2) ≤ (2 * (m + 1 / 2) ^ 4) * (m + 1 / 2) :=
          mul_le_mul_of_nonneg_right hka hmhalf.le
        exact mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
    _ = 2 * (m + 1 / 2) ^ 5 * ρ ^ ((1 : ℝ) / 2) := by ring

omit [DecidableEq ι₀] [DecidableEq F₀] in
/-- **Affine capture in the natural `ℓ`-shape discharges the numeric residual.** Per-stack
capture lists of size `≤ L` with `L ≤ (m+½)/√ρ₊` — the exact shape of the GS `Y`-degree /
list-size bound — imply `JohnsonNumericBound` (for `k ≤ n`). The only remaining input to
the Johnson MCA bound is the capture data itself. -/
theorem johnsonNumericBound_of_affine_capture_of_list_shape
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hk : k ≤ Fintype.card ι₀)
    (hL : (L : ℝ) ≤ (hab25M (Fintype.card ι₀) k η + 1 / 2) /
      hab25RhoPlus (Fintype.card ι₀) k ^ ((1 : ℝ) / 2))
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ pairs : Finset (F₀[X] × F₀[X]), pairs.card ≤ L ∧
        (∀ ab ∈ pairs, ab.1.natDegree < k ∧ ab.2.natDegree < k) ∧
        ∀ γ ∈ hab25McaBadScalars domain k δ u,
          ∃ ab ∈ pairs, AffineCaptured domain k δ u γ ab) :
    JohnsonNumericBound domain k η δ := by
  classical
  exact johnsonNumericBound_of_affine_capture_of_list_le domain k η δ L hη hδ
    (le_trans hL (list_shape_le_budget η Fintype.card_pos hk)) hdata

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hab25RhoPlus_le_two
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnson_key_arith
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.list_shape_le_budget
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_affine_capture_of_list_shape
