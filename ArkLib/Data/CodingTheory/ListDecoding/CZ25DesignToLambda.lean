/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended

/-!
# ABF26 T3.4 [CZ25 Thm B.5]: subspace-design ⟹ list-size bound (design→Λ conversion)

This file attacks **ABF26 Theorem 3.4** [CZ25 Thm B.5], the general
"τ-subspace-design ⟹ list-decodable up to capacity" theorem, recorded in
`ListDecoding/Bounds.lean` as the external admit `subspaceDesign_list_decoding_cz25`.

The ground-truth statement shape (the one consumed by
`CZ25CapacityReduction.frs_list_decoding_capacity_cz25_of_T34_T218`, which already turns
T3.4 + T2.18 into the C3.5 folded-RS capacity bound) is, for a τ-subspace-design code
`C : Submodule F (ι → Fin s → F)`, every `η' > 0`, and with `r₀ := ⌊1/η'⌋`:

  `Λ(C, 1 - τ(r₀) - η') ≤ (1 - τ(r₀)) / η'`   (as `ENNReal`).

## The CZ25 / Guruswami–Kopparty argument (paper level)

Fix a received word `f`. Let `δ := 1 - τ(r₀) - η'` be the decoding radius and
`L := closeCodewordsRel C f δ = { c ∈ C : δᵣ(f, c) ≤ δ }` the candidate list; write
`ℓ := |L|`. Each `c ∈ L` agrees with `f` on at least `(1 - δ)·n = (τ(r₀) + η')·n`
coordinates (blocks of `Fin s → F`).

The subspace-design property bounds the *total agreement* the list can carry. Pick
`c₀ ∈ L` and form the `F`-subspace `A := span{ c - c₀ : c ∈ L } ≤ C`, of dimension
`m ≤ ℓ - 1`. The design inequality at radius `m` (valid once `m ≤ r₀`) reads
`(Σ_i dim A_i)/n ≤ m · τ(r₀)`, where `A_i = A ∩ ker(eval_i)` collects the differences
vanishing at block `i`. Double-counting per-coordinate agreement against this design
budget, and feeding back `m ≤ ℓ - 1`, collapses to the *agreement-budget* inequality

  `ℓ · η' ≤ 1 - τ(r₀)`,   i.e.   `ℓ ≤ (1 - τ(r₀)) / η'`.

(Each list element consumes a fresh `η'·n` slice of an agreement budget capped at
`(1 - τ(r₀))·n`.) Maximising over `f` gives the `Λ` bound.

## What is proven here vs. the residual

The genuinely substrate-heavy step is the **per-word real dimension count**: the affine
span `A`, the per-coordinate agreement subspaces `A_i`, and the collapse of the design
inequality to `ℓ ≤ (1 - τ(r₀))/η'`. Mathlib has no subspace-design / agreement-span API,
so this kernel is isolated as the named residual

  `CZ25DimensionCount` — the per-word real bound `|L| ≤ (1 - τ(r₀))/η'`.

**Everything else is proven here, `sorry`-free and axiom-clean:**

* the negative-radius / out-of-range edge cases (`δ < 0 ⟹ L = ∅`), which are handled
  *outside* the residual so the residual only ever faces the non-degenerate regime;
* the `ℝ`-membership bridge for `closeCodewordsRel` (relating `δᵣ(f,c) ≤ δ` to the real
  inequality `(δᵣ(f,c) : ℝ) ≤ δ`);
* the packaging of the per-word `ncard` bounds into the maximised `Λ` via
  `Lambda_le_of_forall_ncard_le`, and the `ENat`→`ENNReal`→`ENNReal.ofReal` coercion.

The headline reduction `subspaceDesign_list_decoding_cz25_of_dimensionCount` derives the
**exact** in-tree T3.4 statement from `CZ25DimensionCount`. This pins the residual to the
irreducible CZ25 dimension-counting core and discharges the conversion's own content.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. Theorem 3.4.
- [CZ25] Thm B.5 (the corrected subspace-design route to capacity list decoding;
  cf. "Optimal Proximity Gap for Folded RS via Subspace Designs", arXiv 2601.10047).
- [GK16] Guruswami-Kopparty. (The classical subspace-design list-decoding analysis.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section EmptyBall

/-! ### Membership bridge for `closeCodewordsRel` at a real radius

These facts are stated for a *general* alphabet `α` (only `Nonempty ι`, `Fintype ι`,
`DecidableEq α` are needed for `relHammingDist`), so that they apply at the block alphabet
`α = Fin s → F` used by subspace-design codes — there `α` is **not** a field. -/

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

/-- Membership in `closeCodewordsRel C f δ` unfolds to codeword-membership together with
the real inequality `(δᵣ(f, c) : ℝ) ≤ δ`. This is the `ℝ`-cast form of the defining
`relHammingBall` condition `Code.relHammingDist f c ≤ δ`. -/
lemma mem_closeCodewordsRel_iff_real
    (C : Set (ι → α)) (f c : ι → α) (δ : ℝ) :
    c ∈ closeCodewordsRel C f δ ↔
      c ∈ C ∧ ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ := by
  simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq]
  -- The two `Code.relHammingDist` occurrences differ only by a (subsingleton) `Decidable`
  -- instance: `relHammingBall` unfolds with `Classical.propDecidable`, the statement uses
  -- the section's `DecidableEq α`.  Reconcile via `congr!`.
  refine and_congr_right (fun _ => ?_)
  congr!

/-- **Negative-radius emptiness.** With radius `δ < 0`, no codeword is `δ`-close: the
relative Hamming distance is nonnegative, so `closeCodewordsRel C f δ = ∅`. This discharges
the degenerate side of T3.4 (where `1 - τ(r₀) < η'`, forcing `δ < 0`) *outside* the
dimension-counting residual. -/
lemma closeCodewordsRel_eq_empty_of_neg
    (C : Set (ι → α)) (f : ι → α) {δ : ℝ} (hδ : δ < 0) :
    closeCodewordsRel C f δ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro c hc
  rw [mem_closeCodewordsRel_iff_real] at hc
  have hnonneg : (0 : ℝ) ≤ ((Code.relHammingDist f c : ℚ≥0) : ℝ) := by positivity
  linarith [hc.2]

/-- `ncard`-form of `closeCodewordsRel_eq_empty_of_neg`: with negative radius the list is
empty, so its cardinality is `0`. -/
lemma ncard_closeCodewordsRel_eq_zero_of_neg
    (C : Set (ι → α)) (f : ι → α) {δ : ℝ} (hδ : δ < 0) :
    (closeCodewordsRel C f δ).ncard = 0 := by
  rw [closeCodewordsRel_eq_empty_of_neg C f hδ, Set.ncard_empty]

end EmptyBall

section CZ25DesignToLambda

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The residual: the CZ25 per-word dimension-counting bound -/

/-- **Residual (CZ25 dimension-counting core).** For a τ-subspace-design code `C` and any
`η' > 0`, every received word `f` has a candidate list of bounded cardinality at the
capacity radius. Concretely, with `r₀ := ⌊1/η'⌋` and the radius
`δ := 1 - τ(r₀) - η'`,

  `|closeCodewordsRel C f δ| ≤ (1 - τ(r₀)) / η'`   (over `ℝ`).

This is the genuine CZ25 / Guruswami–Kopparty content (the affine-span dimension count
against the subspace-design budget; see the file header), and the *only* admitted
ingredient of T3.4. It is stated for the non-degenerate regime that the conversion
actually feeds it: when `δ < 0` the list is provably empty (handled in-tree by
`ncard_closeCodewordsRel_eq_zero_of_neg`), so this residual is only ever invoked with
`(1 - τ(r₀))/η' ≥ 0`. -/
def CZ25DimensionCount
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η' : ℝ) (_hη' : 0 < η') : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η')) - η' →
    ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η')) - η')).ncard : ℝ)
      ≤ (1 - τ (Nat.floor (1 / η'))) / η'

/-! ### The reduction: residual ⟹ T3.4 -/

/-- **ABF26 Theorem 3.4 [CZ25 Thm B.5] — reduction form.**

Given the CZ25 dimension-counting core `CZ25DimensionCount` as a hypothesis, the full
in-tree T3.4 `Λ`-bound follows. We package the per-word real `ncard` bounds into the
maximised `Λ` via `Lambda_le_of_forall_ncard_le` and the `ENat`→`ENNReal.ofReal`
coercion, with the negative-radius regime discharged in-tree. No `sorry`, no new axioms;
the entire residual lives in `hDC`. -/
theorem subspaceDesign_list_decoding_cz25_of_dimensionCount
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (η : ℝ) (hη_pos : 0 < η)
    (hDC : CZ25DimensionCount s τ C h η hη_pos) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) := by
  -- Abbreviations matching the residual / statement.
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδ
  set bound : ℝ := (1 - τ r₀) / η with hbound
  -- Expand `Λ` as an `iSup` over received words `f`, pushed through `ENat.toENNReal`.
  simp only [Lambda, ENat.toENNReal_iSup]
  refine iSup_le (fun f => ?_)
  -- For each word `f`, bound the point-list `ncard` (coerced to `ENNReal`) by `ofReal bound`.
  set m : ℕ := (closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard with hm
  -- Rewrite the `ℕ∞`→`ENNReal` coercion of the natural `m` as `ENNReal.ofReal m`.
  have hcast : ENat.toENNReal ((m : ℕ) : ℕ∞) = ENNReal.ofReal (m : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  rw [hcast]
  -- Split on the sign of the radius.
  rcases lt_or_ge δ 0 with hδneg | hδnonneg
  · -- Negative radius: the list is empty, so `m = 0` and `ofReal 0 = 0 ≤ ofReal bound`.
    have hm0 : m = 0 := by rw [hm]; exact ncard_closeCodewordsRel_eq_zero_of_neg _ _ hδneg
    rw [hm0]
    simp
  · -- Non-degenerate radius: the dimension-counting residual gives the real bound.
    have hreal : (m : ℝ) ≤ bound := hDC f hδnonneg
    exact ENNReal.ofReal_le_ofReal hreal

end CZ25DesignToLambda

end CodingTheory
