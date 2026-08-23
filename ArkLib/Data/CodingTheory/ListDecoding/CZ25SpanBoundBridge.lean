/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import ArkLib.ToMathlib.CZ25DimensionCountProof
import Mathlib.InformationTheory.Hamming

/-!
# CZ25 dimension count: the coordinate-fiber bridge to the guarded span bound (issue #93)

This file wires together the two already-landed halves of the CZ25 / Guruswami–Wang
dimension count (issue #93) and reduces the guarded residual `CZ25SpanBound'`
(`ListDecoding/CZ25SpanDimension.lean`) to a *single* precisely-named bridge obligation,
`CZ25CoordFiberCap` — the affine-flat coordinate-fiber cap on the agreement table.

## Structure

* **agreement lower bound** (already landed, `ToMathlib/CZ25DimensionCountProof.lean`):
  `|L| · (1 - δ) · n ≤ ∑_i #{c ∈ L : c i = f i}` via
  `sum_agree_ge_of_subset_closeCodewordsRel` + the Fubini swap `sum_agree_swap`.
* **design half** (already landed, `ListDecoding/CZ25SpanDimension.lean`):
  `∑_i |S i| ≤ m · τ(r₀) · n` via `sum_card_vanishing_le_design`.
* **bridge residual** (new, here): `CZ25CoordFiberCap` packages the affine-flat upper bound
  `∑_i #{c ∈ L : c i = f i} ≤ ((|L| - 1)·τ(r₀) + 1)·n` that the design half supplies through
  the recentred-span construction. This is the genuinely-deep Guruswami–Wang content that
  `CZ25SpanDimension.lean` (lines 292–302) documents as having no shortcut over the design
  budget.
* **derivation** (new, here): `cz25SpanBound'_of_coordFiberCap` proves `CZ25SpanBound'` from
  the bridge alone, by the elementary charge collapse; composed with the existing reduction
  `subspaceDesign_list_decoding_cz25_of_spanBound'` this gives the in-tree T3.4 `Λ`-bound from
  the single bridge residual (`subspaceDesign_list_decoding_cz25_of_coordFiberCap`).
* **trivial slice** (new, here): `cz25SpanBound'_of_le_one` discharges `CZ25SpanBound'`
  unconditionally on any code whose candidate lists never exceed one codeword
  (unique-decoding / sub-Johnson regime), with no design content.

Everything here is `sorry`-free; the only admitted input is the named bridge residual
`CZ25CoordFiberCap`, whose docstring states exactly the affine-flat obligation that remains.

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section Bridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The per-coordinate agreement-table sum `∑_i #{c ∈ L : c i = f i}` over the candidate
list `L`, realised as a finite set `Lset`, cast to `ℝ`. This is the coordinate-first form
of the agreement double count: the right-hand side of `sum_agree_swap`, lower-bounded by
`|L| · (1 - δ) · n` (`sum_agree_ge_of_subset_closeCodewordsRel`) and upper-bounded by the
design budget (`CZ25CoordFiberCap`). -/
noncomputable def coordAgreeSum (s : ℕ)
    (f : ι → Fin s → F) (Lset : Finset (ι → Fin s → F)) : ℝ :=
  ∑ i : ι, ((Lset.filter (fun c => c i = f i)).card : ℝ)

/-- **Bridge residual: the affine-flat coordinate-fiber cap (the genuine GW content).**
For each received word `f` on the non-degenerate regime `δ := 1 - τ(r₀) - η ≥ 0`, the
candidate list `L := closeCodewordsRel C f δ` (realised as a finite set `Lset`) satisfies the
design-budget cap on the coordinate agreement table

  `∑_i #{c ∈ L : c i = f i} ≤ ((|L| - 1) · τ(r₀) + 1) · n`.

**Why this is the irreducible kernel.** Recentre the list at a base `c₀ ∈ L` and form the
`F`-subspace `A := span{c - c₀ : c ∈ L}`, of dimension `m ≤ |L| - 1`. For each coordinate `i`,
the list elements agreeing with `f` at `i` fill an *affine flat* whose direction space lies in
`A ⊓ ker eval_i`; the design half (`sum_card_vanishing_le_design`) caps the total *direction*
mass `∑_i dim(A ⊓ ker eval_i) ≤ m · τ(r₀) · n`, and each coordinate contributes one affine
base point (`+ 1 · n`). Monotonicity in `m` (using `τ(r₀) ≥ 0` for genuine designs) yields the
self-contained `|L| - 1` form. This is *exactly* the affine-flat-vs-linear content that
`CZ25SpanDimension.lean` (lines 292–302) documents as having **no shortcut** over the design
budget: past the Johnson radius `#{c ∈ L : c_i = f_i}` is `q^{dim}` (a full affine flat), **not**
`dim + 1`, so the naive pointwise double count is provably false and the cap must be stated at
the affine-flat level. This residual isolates that obligation and nothing else; everything
around it is discharged (`cz25SpanBound'_of_coordFiberCap`). -/
def CZ25CoordFiberCap
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ Lset : Finset (ι → Fin s → F),
      (∀ c, c ∈ Lset ↔ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)) ∧
      coordAgreeSum s f Lset ≤
        (((Lset.card : ℝ) - 1) * τ (Nat.floor (1 / η)) + 1) * Fintype.card ι

/-- **Bridge ⟹ guarded span bound (`CZ25CoordFiberCap ⟹ CZ25SpanBound'`).** From the
coordinate-fiber cap and the already-landed agreement lower bound
(`sum_agree_ge_of_subset_closeCodewordsRel` composed through `sum_agree_swap`), the guarded
residual `CZ25SpanBound'` follows by the elementary charge collapse:

  `|L| · (τ(r₀) + η) · n ≤ ∑_i #{c : c_i = f_i} ≤ ((|L| - 1)·τ(r₀) + 1) · n`

cancels `n > 0` and rearranges to `|L| · η ≤ 1 - τ(r₀)`, whence the witness `m := |L| - 1`
satisfies both `|L| ≤ m + 1` and `m · η ≤ 1 - τ(r₀) - η`. No `sorry`; the only admitted input
is the named bridge `hCap`. -/
theorem cz25SpanBound'_of_coordFiberCap
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hCap : CZ25CoordFiberCap s τ C h η hη) :
    CZ25SpanBound' s τ C h η hη := by
  intro f hδ
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδdef
  obtain ⟨Lset, hmem, hcap⟩ := hCap f hδ
  have hset : (Lset : Set (ι → Fin s → F)) =
      closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ := by
    ext c; exact hmem c
  have hncard : (closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard = Lset.card := by
    rw [← hset, Set.ncard_coe_finset]
  have hagree_lb : (Lset.card : ℝ) * ((1 - δ) * Fintype.card ι) ≤
      ∑ c ∈ Lset, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) := by
    apply sum_agree_ge_of_subset_closeCodewordsRel (C := (C : Set (ι → Fin s → F))) f Lset
    intro c hc
    exact (hmem c).mp hc
  have hswap : (∑ c ∈ Lset, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ)) =
      coordAgreeSum s f Lset := by
    rw [coordAgreeSum]
    have h2 : ((∑ c ∈ Lset, (Finset.univ.filter (fun i => c i = f i)).card : ℕ) : ℝ) =
        ((∑ i : ι, (Lset.filter (fun c => c i = f i)).card : ℕ) : ℝ) := by
      exact_mod_cast sum_agree_swap (ι := ι) (α := Fin s → F) f Lset
    push_cast at h2
    exact h2
  have h1mδ : (1 - δ) = τ r₀ + η := by rw [hδdef]; ring
  rw [hswap, h1mδ] at hagree_lb
  have hchain : (Lset.card : ℝ) * ((τ r₀ + η) * Fintype.card ι) ≤
      (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := le_trans hagree_lb hcap
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hchain' : (Lset.card : ℝ) * (τ r₀ + η) ≤ ((Lset.card : ℝ) - 1) * τ r₀ + 1 := by
    have hLe : (Lset.card : ℝ) * (τ r₀ + η) * Fintype.card ι ≤
        (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
      simpa [mul_assoc] using hchain
    exact le_of_mul_le_mul_right hLe hn_pos
  have hLη : (Lset.card : ℝ) * η ≤ 1 - τ r₀ := by nlinarith [hchain']
  refine ⟨Lset.card - 1, ?_, ?_⟩
  · rw [hncard]
    have hnat : Lset.card ≤ (Lset.card - 1) + 1 := Nat.le_succ_of_pred_le le_rfl
    have hc : (Lset.card : ℝ) ≤ (((Lset.card - 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hc ⊢; linarith
  · rcases Nat.eq_zero_or_pos Lset.card with h0 | hpos
    · simp only [h0, Nat.zero_sub, Nat.cast_zero, zero_mul]
      exact hδ
    · have hcast : ((Lset.card - 1 : ℕ) : ℝ) = (Lset.card : ℝ) - 1 := by
        rw [Nat.cast_sub hpos]; simp
      rw [hcast, hδdef]
      nlinarith [hLη, le_of_lt hη]

/-- **Trivial-list discharge of `CZ25SpanBound'`.** If for every received word the candidate
list at the capacity radius has at most one codeword, then the guarded residual holds with the
witness `m = 0` (`|L| ≤ 1 = 0 + 1`, and `0 · η = 0 ≤ δ` is the guard). This covers any code
whose decoding radius stays within the unique-decoding / sub-Johnson regime — the easy slice
of T3.4 — with no design-budget content. Reusable, `sorry`-free, axiom-clean. -/
theorem cz25SpanBound'_of_le_one
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard ≤ 1) :
    CZ25SpanBound' s τ C h η hη := by
  intro f hδ
  refine ⟨0, ?_, ?_⟩
  · have hr : ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η)) - η)).ncard : ℝ) ≤ 1 := by exact_mod_cast hle f
    simpa using hr
  · simpa using hδ

/-- **In-tree T3.4 [CZ25 Thm B.5] from the coordinate-fiber bridge.** Composing
`cz25SpanBound'_of_coordFiberCap` with the existing reduction
`subspaceDesign_list_decoding_cz25_of_spanBound'`, the exact in-tree `Λ`-bound follows from the
single named bridge residual `CZ25CoordFiberCap` (the affine-flat fiber cap) directly — the
agreement lower bound, the Fubini swap, the charge collapse, the `δ < 0` empty-list regime, and
the `ncard`/`Lambda` packaging all discharged. No `sorry`, no new axioms. -/
theorem subspaceDesign_list_decoding_cz25_of_coordFiberCap
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hCap : CZ25CoordFiberCap s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_spanBound' s τ C h η hη
    (cz25SpanBound'_of_coordFiberCap s τ C h η hη hCap)

end Bridge

end CodingTheory

#print axioms CodingTheory.cz25SpanBound'_of_coordFiberCap
#print axioms CodingTheory.cz25SpanBound'_of_le_one
#print axioms CodingTheory.subspaceDesign_list_decoding_cz25_of_coordFiberCap
