/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowCapstone

/-!
# The boundary-slice reach of the window pencil law (#371)

The window pencil law (`badScalars_card_le_of_anchor`) carries **no below-UDR
hypothesis**: the row selection `J` need not be injective, so a duplicated-row
square selection anchors the argument at the **boundary slice `n = 2w + k`** —
the first radius past unique decoding, where the F₁₇ explosion band lives.
Probe record (`probe_wb_boundary_slice_anchor.py`): at `(17,8,4,2)` and
`(37,12,8,2)` every sampled rational stack is anchored, and the adjacent-pair
ceiling family at `(37,12,8,2)` — `|BAD| = 12 = n` — is anchored, i.e. the
`n`-sized boundary explosion is INSIDE the proven budget `(w+1)+n(w+1)+1`.

This file pins the reach exactly:

* `windowPencil_adjugate_eq_zero_of_lt_boundary` — **the no-go**: strictly above
  the boundary (`n + 1 ≤ 2w + k`), every adjugate entry of every square
  row-selection vanishes identically (pigeonhole: even after deleting one row,
  a repeated pencil row survives), so `WindowPencilAnchored` is unsatisfiable
  and the law is vacuous there.  Marching further needs the corank-≥2
  (compound-matrix / cyclic-kernel) generalization.
* `epsMCA_le_boundary_slice` — **the reach**: at the boundary radius
  `δ = w/n`, under the `UnanchoredLinear` residual alone,
  `ε_mca ≤ ((w+1) + n(w+1) + 1)/q` — the first counting law past UDR on this
  route, production-silent at `q ≥ n²·2¹²⁸`.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- **The no-go above the boundary slice.**  For `n + 1 ≤ 2w + k`, every square
row-selection of the window pencil repeats a row even after deleting any single
one, so the whole adjugate vanishes: anchoring is impossible strictly above the
boundary `n = 2w + k`. -/
theorem windowPencil_adjugate_eq_zero_of_lt_boundary (dom : Fin n ↪ F)
    {k w : ℕ} (hn : n + 1 ≤ 2 * w + k) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ cs : WCol n k w) :
    ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id).adjugate cs c₀ = 0 := by
  classical
  rw [Matrix.adjugate_apply]
  -- the non-updated rows live in `Fin (3w+k)`; there are `N − 1` of them with
  -- `N − 1 = (w+1)+(w+k)+(3w+k−n) − 1 > 3w+k` when `n + 1 ≤ 2w + k`
  have hcard : Fintype.card (Fin (3 * w + k))
      < ((Finset.univ : Finset (WCol n k w)).erase c₀).card := by
    have h1 : Fintype.card (WCol n k w) = (w + 1) + ((w + k) + (3 * w + k - n)) := by
      simp [WCol]
    have h2 : ((Finset.univ : Finset (WCol n k w)).erase c₀).card
        = Fintype.card (WCol n k w) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ c₀), Finset.card_univ]
    rw [h2, h1, Fintype.card_fin]
    omega
  obtain ⟨a, ha, a', ha', hne, hJ⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun a _ => Finset.mem_univ (J a))
  have hac : a ≠ c₀ := Finset.ne_of_mem_erase ha
  have hac' : a' ≠ c₀ := Finset.ne_of_mem_erase ha'
  refine Matrix.det_zero_of_row_eq hne ?_
  funext b
  rw [Matrix.updateRow_apply, if_neg hac, Matrix.updateRow_apply, if_neg hac']
  simp only [Matrix.submatrix_apply, id_eq, hJ]

section Consumer

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The boundary-slice law**: at `n = 2w + k` — the first radius past unique
decoding — under the `UnanchoredLinear` residual alone,
`ε_mca(RS, δ) ≤ ((w+1) + n(w+1) + 1)/q` for every `δ ≤ w/n`.  The first
counting law past UDR on the pencil route; the probe-confirmed anchored class
includes the `n`-sized adjacent-pair explosion family. -/
theorem epsMCA_le_boundary_slice (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hb : n = 2 * w + k) {δ : ℝ≥0}
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hres : UnanchoredLinear dom k w δ) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (((w + 1) + n * (w + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_below_udr_of_unanchoredLinear dom hk (by omega) hδn hres

end Consumer
end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.windowPencil_adjugate_eq_zero_of_lt_boundary
#print axioms ProximityGap.WBPencil.epsMCA_le_boundary_slice
