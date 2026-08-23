/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Claim1
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArith

/-!
# Hab25 §3 — end-to-end wiring: per-stack Claim-1 cells ⟹ the Johnson numeric residual

This file closes the wiring between the proven Claim-1 dichotomy (`Hab25Claim1.lean`) and
the proven numeric chain (`Hab25JohnsonNumericBridge.lean` / `Hab25JohnsonArith.lean`), at
the **sharp** per-stack count `|E_u| ≤ ℓ·n` (the integer-sharp bound the in-tree
`johnsonBoundReal` closed form is calibrated to — sharper than the paper's headline
`(ℓ⁷/3)(ρn)²`, which it implies):

* `bad_card_le_of_claim1_cells` — per-stack: a cell decomposition of the bad scalars into
  `≤ L` cells, each subject to the Claim-1 dichotomy at threshold `T := n` (the
  [BCI⁺20 Steps 5–7] capture-above-`n` hypothesis), gives `|E_u| ≤ L·n` outright;
* `johnsonNumericBound_of_claim1_cells` — the capstone: per-stack cell data with the cell
  count `L` in the GS list-size shape `L ≤ (m+½)/√ρ₊` discharges `JohnsonNumericBound`
  end-to-end (counting → real edge → closed form), with **no remaining numeric or
  combinatorial obligations**.

After this file, the complete derivation tree of the Johnson-range MCA bound
(`JohnsonNumericBound`, hence `rs_epsMCA_johnson_range_bchks25` via the proven
`rs_epsMCA_johnson_range_bchks25_of_johnsonNumericBound`) rests on **exactly one**
mathematical input, per stack and per cell:

> *capture above `n`*: if a cell exceeds `n` scalars, one degree-`< k` affine pair
> captures all of them — which is [BCI⁺20, ePrint 2020/654] Claim 5.7 (pigeonhole, gives
> the incidence `|S_{x₀,R,H}| ≥ |S|/D_Y > 2D_Y²·D_X·D_{YZ}`) + Steps 5–7 (the power-series
> coefficients `α_t` of the Hensel branch vanish for `t > k` by the `Λ`-weight zero count,
> Claim 5.8, and are `Z`-linear, Claim 5.9) + Appendix C (the inseparable shell).
> The in-tree `BCIKS20/HenselNumerator` (`βHensel`, `W`, `ξ`, `ζ`, `Λ`-weight) stream
> (#138/#139) formalizes exactly these objects; its open cores are this statement.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

attribute [local instance] Classical.propDecidable

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

omit [DecidableEq ι₀] in
/-- **Per-stack sharp count from Claim-1 cells at threshold `n`.** A decomposition of the
stack's bad scalars into `≤ L` cells, each satisfying the Claim-1 dichotomy hypothesis at
`T := n` (capture above `n` — the [BCI⁺20 Steps 5–7] output), bounds the bad set by `L·n`:
each cell is `≤ n` by `claim1_dichotomy`, and the union bound finishes. -/
theorem bad_card_le_of_claim1_cells (domain : ι₀ ↪ F₀) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F₀ (Fin 2) ι₀)
    {Idx : Type}
    (Index : Finset Idx) (Ecell : Idx → Finset F₀) (L : ℕ)
    (hL : Index.card ≤ L)
    (hcover : (Finset.univ.filter
      (fun γ : F₀ => mcaEvent (F := F₀)
        ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)) ⊆
      Index.biUnion Ecell)
    (hsteps57 : ∀ ij ∈ Index, Fintype.card ι₀ < (Ecell ij).card →
      ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
        ∀ γ ∈ Ecell ij,
          AffineCaptured domain k δ u γ (a, b)) :
    (Finset.univ.filter
      (fun γ : F₀ => mcaEvent (F := F₀)
        ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)).card ≤
      L * Fintype.card ι₀ := by
  classical
  exact theorem2_of_claim1_cells domain k δ u _ Index Ecell L (Fintype.card ι₀)
    hL (le_refl _) hcover hsteps57

omit [DecidableEq ι₀] in
/-- **End-to-end: per-stack Claim-1 cells in the GS list shape discharge the Johnson
numeric residual.** Given, for every word stack, a cell decomposition of its bad scalars
with `≤ L` cells (`L` within the GS list-size shape `(m+½)/√ρ₊`, e.g. `L = D_Y < ℓ`) and
the per-cell capture-above-`n` hypothesis ([BCI⁺20 Claim 5.7 + Steps 5–7 + App. C]), the
previously-atomic `JohnsonNumericBound` follows with no further obligations: the per-stack
count is `≤ L·n` (`bad_card_le_of_claim1_cells`), and `L·n/|F| ≤ johnsonBoundReal` is the
proven closed-form arithmetic (`list_shape_le_budget` +
`nat_mul_card_div_le_johnsonBoundReal`), entering through the in-tree S11 bridge
`JohnsonNumericBound.of_card_le_nat`. -/
theorem johnsonNumericBound_of_claim1_cells
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hk : k ≤ Fintype.card ι₀)
    (hL : (L : ℝ) ≤ (hab25M (Fintype.card ι₀) k η + 1 / 2) /
      hab25RhoPlus (Fintype.card ι₀) k ^ ((1 : ℝ) / 2))
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ (Idx : Type) (Index : Finset Idx) (Ecell : Idx → Finset F₀),
        Index.card ≤ L ∧
        (Finset.univ.filter
          (fun γ : F₀ => mcaEvent (F := F₀)
            ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)) ⊆
          Index.biUnion Ecell ∧
        ∀ ij ∈ Index, Fintype.card ι₀ < (Ecell ij).card →
          ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
            ∀ γ ∈ Ecell ij,
              AffineCaptured domain k δ u γ (a, b)) :
    JohnsonNumericBound domain k η δ := by
  classical
  refine JohnsonNumericBound.of_card_le_nat domain k η δ (L * Fintype.card ι₀) ?_ ?_
  · -- the closed-form arithmetic: `L·n/|F| ≤ johnsonBoundReal`
    have h := nat_mul_card_div_le_johnsonBoundReal domain k η δ L
      (le_trans hL (list_shape_le_budget η Fintype.card_pos hk))
    exact_mod_cast h
  · intro u
    obtain ⟨Idx, Index, Ecell, hLcard, hcover, hsteps57⟩ := hdata u
    exact bad_card_le_of_claim1_cells domain k δ u Index Ecell L hLcard hcover hsteps57

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.bad_card_le_of_claim1_cells
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_claim1_cells
