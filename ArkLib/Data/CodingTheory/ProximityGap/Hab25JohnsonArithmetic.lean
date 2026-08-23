/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture

/-!
# Hab25 §3 — the closed-form Johnson arithmetic for the per-stack count

The affine-capture route (`Hab25AffineCapture.lean`) and the in-tree S11 bridge consume one
remaining *numeric* input: `L·n/|F| ≤ johnsonBoundReal domain k η δ` for the per-stack list
bound `L`. This file discharges that input by closed-form arithmetic on the bound

  `johnsonBoundReal = ((2(m+½)⁵ + 3(m+½)δρ₊) / (3ρ₊^{3/2}) · n + (m+½)/√ρ₊) / |F|`,

`ρ₊ := k/n + 1/n`, `m := max(⌈√ρ₊/(2η)⌉, 3)`:

* `hab25RhoPlus` / `hab25M` — the parameters as standalone definitions, with the
  definitional identity `johnsonBoundReal_eq` (zeta-expanding the `let`s);
* positivity: `hab25RhoPlus_pos`, `hab25M_ge_three`;
* **`nat_mul_card_div_le_johnsonBoundReal`** — the numeric edge: whenever the list bound
  satisfies `L ≤ 2(m+½)⁵ / (3ρ₊^{3/2})` (the paper's `ℓ`-budget; note `2(m+½)⁵/(3ρ₊^{3/2})
  ≥ 2·3.5⁵/3·ρ₊^{-3/2} ≥ 350` for any rate `ρ₊ ≤ 1`), the per-stack count scales into the
  Johnson bound: `(L·n : ℕ)/|F| ≤ johnsonBoundReal`. The `δ`-term and the additive
  `(m+½)/√ρ₊` term are simply nonnegative slack.
* `johnsonNumericBound_of_affine_capture_of_list_le` — composition with the affine-capture
  route: per-stack capture lists within the `ℓ`-budget discharge `JohnsonNumericBound`
  outright.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- The Hab25 rate-plus parameter `ρ₊ = k/n + 1/n` (with `n` the domain size). -/
noncomputable def hab25RhoPlus (n k : ℕ) : ℝ := (k : ℝ) / (n : ℝ) + 1 / (n : ℝ)

/-- The Hab25 multiplicity parameter `m = max(⌈√ρ₊/(2η)⌉, 3)`. -/
noncomputable def hab25M (n k : ℕ) (η : ℝ≥0) : ℝ :=
  max ⌈(hab25RhoPlus n k ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3

/-- `johnsonBoundReal`, zeta-expanded through `hab25RhoPlus`/`hab25M`. -/
theorem johnsonBoundReal_eq (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) :
    johnsonBoundReal domain k η δ =
      ((2 * (hab25M (Fintype.card ι₀) k η + 1/2) ^ 5 +
          3 * (hab25M (Fintype.card ι₀) k η + 1/2) * δ * hab25RhoPlus (Fintype.card ι₀) k)
        / (3 * hab25RhoPlus (Fintype.card ι₀) k ^ ((3 : ℝ) / 2)) * (Fintype.card ι₀ : ℝ)
      + (hab25M (Fintype.card ι₀) k η + 1/2)
        / hab25RhoPlus (Fintype.card ι₀) k ^ ((1 : ℝ) / 2))
      / (Fintype.card F₀ : ℝ) := rfl

theorem hab25RhoPlus_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < hab25RhoPlus n k := by
  have h1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
  rw [hab25RhoPlus]
  linarith

theorem hab25M_ge_three (n k : ℕ) (η : ℝ≥0) : (3 : ℝ) ≤ hab25M n k η := by
  rw [hab25M]
  exact_mod_cast le_max_right _ _

/-- **The closed-form numeric edge.** If the per-stack list bound `L` is within the
`ℓ`-budget `2(m+½)⁵ / (3ρ₊^{3/2})`, then `(L·n : ℕ)/|F| ≤ johnsonBoundReal`: the
`δ`-cross-term and the additive `(m+½)/√ρ₊` term are nonnegative slack. -/
theorem nat_mul_card_div_le_johnsonBoundReal
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hL : (L : ℝ) ≤ 2 * (hab25M (Fintype.card ι₀) k η + 1/2) ^ 5 /
      (3 * hab25RhoPlus (Fintype.card ι₀) k ^ ((3 : ℝ) / 2))) :
    ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ := by
  have hn : 0 < Fintype.card ι₀ := Fintype.card_pos
  set n : ℕ := Fintype.card ι₀ with hn_def
  set ρ : ℝ := hab25RhoPlus n k with hρ_def
  set m : ℝ := hab25M n k η with hm_def
  have hρ_pos : 0 < ρ := hab25RhoPlus_pos hn k
  have hρ32_pos : (0 : ℝ) < ρ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hρ_pos _
  have hρ12_pos : (0 : ℝ) < ρ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hρ_pos _
  have hm3 : (3 : ℝ) ≤ m := hab25M_ge_three n k η
  have hm_half_pos : (0 : ℝ) < m + 1/2 := by linarith
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  -- the coefficient of `n` dominates `L`
  have hcoeff : (L : ℝ) ≤
      (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * (δ : ℝ) * ρ) / (3 * ρ ^ ((3 : ℝ) / 2)) := by
    refine le_trans hL ?_
    have hcross : (0 : ℝ) ≤ 3 * (m + 1/2) * (δ : ℝ) * ρ := by positivity
    have hden : (0 : ℝ) ≤ 3 * ρ ^ ((3 : ℝ) / 2) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hden
  -- the trailing term is nonnegative
  have htail : (0 : ℝ) ≤ (m + 1/2) / ρ ^ ((1 : ℝ) / 2) := by positivity
  -- assemble
  rw [johnsonBoundReal_eq, ← hn_def, ← hρ_def, ← hm_def]
  have hFpos : (0 : ℝ) < (Fintype.card F₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hFpos]
  push_cast
  have hnum : (L : ℝ) * (n : ℝ) ≤
      (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * (δ : ℝ) * ρ) /
        (3 * ρ ^ ((3 : ℝ) / 2)) * (n : ℝ) := by
    refine mul_le_mul_of_nonneg_right hcoeff ?_
    positivity
  linarith

/-- **Affine capture within the `ℓ`-budget discharges the numeric residual outright.**
Per-stack capture lists of size `≤ L` with `L` inside the closed-form budget
`2(m+½)⁵/(3ρ₊^{3/2})` imply `JohnsonNumericBound` — no numeric side condition remains. -/
theorem johnsonNumericBound_of_affine_capture_of_list_le
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hL : (L : ℝ) ≤ 2 * (hab25M (Fintype.card ι₀) k η + 1/2) ^ 5 /
      (3 * hab25RhoPlus (Fintype.card ι₀) k ^ ((3 : ℝ) / 2)))
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ pairs : Finset (F₀[X] × F₀[X]), pairs.card ≤ L ∧
        (∀ ab ∈ pairs, ab.1.natDegree < k ∧ ab.2.natDegree < k) ∧
        ∀ γ ∈ hab25McaBadScalars domain k δ u,
          ∃ ab ∈ pairs, AffineCaptured domain k δ u γ ab) :
    JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_affine_capture domain k η δ L hη hδ hdata
    (nat_mul_card_div_le_johnsonBoundReal domain k η δ L hL)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonBoundReal_eq
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.nat_mul_card_div_le_johnsonBoundReal
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_affine_capture_of_list_le
