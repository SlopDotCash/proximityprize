/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import ArkLib.Data.CodingTheory.Basic.Distance
import Mathlib.InformationTheory.Hamming

/-!
# CZ25 dimension-count: reusable agreement-coordinate bricks (issue #93)

Reusable sub-bricks toward the greedy-chain argument of `CodingTheory.CZ25DimensionCount`
(`ListDecoding/CZ25DesignToLambda.lean:152`), the per-received-word real bound
`|closeCodewordsRel C f δ| ≤ (1 - τ(r₀))/η` against an `IsSubspaceDesign` budget.

The genuine core is the Guruswami-Wang iterative charge, which `CZ25SpanDimension.lean`
documents as having no shortcut over the design budget (the naive single-base-point witnesses
are *provably false* there). This file lands the genuinely-reusable, axiom-clean ingredients
that the greedy chain (step 1 of the issue-#93 proof architecture) consumes:

* **agreement-coordinate lower bound** — for `c ∈ closeCodewordsRel C f δ`, the number of
  block coordinates `i : ι` where `c i = f i` is at least `(1 - δ)·n`. Equivalently, the
  disagreement count is at most `δ·n`. This is the "agreement ≥ (τ(r₀)+η)·n" datum that
  the greedy chain's step-1 charge consumes.
* **recentred-difference vanishing count** — if two close codewords `c` and `c₀` both agree
  with `f` on large coordinate sets, then their difference `c - c₀` vanishes on the
  intersection of those agreement sets, giving at least `(1 - 2δ)·n` vanishing coordinates.
  The list-level aggregate and coordinate-first swap put this in the table form consumed by
  the design budget.
* **recentred span setup** — for a submodule code `C`, close codewords are elements of `C`,
  so every difference `c - c₀` is in `C` and the finite recentred span lies below `C`.

All results are stated for the block alphabet `Fin s → F` (so `α = Fin s → F`, not a field),
matching the subspace-design coordinate structure, and are `sorry`-free / axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami-Wang. *Linear-algebraic list decoding of folded Reed-Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section AgreementCount

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

/-- **Disagreement count as a `Finset.filter` cardinality.** The Hamming distance
`hammingDist f c = #{i | f i ≠ c i}` equals the cardinality of the filtered universe of
coordinates on which `f` and `c` disagree. This is the `Finset.filter`-form of the Mathlib
definition `hammingDist x y = #{i | x i ≠ y i}`, made explicit so downstream agreement
counts can split the universe into agreeing/disagreeing parts. -/
lemma hammingDist_eq_card_filter_ne (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card := by
  simpa [Code.disagreementCols] using
    Code.hammingDist_eq_disagreementCols_card (u := f) (v := c)

/-- **Agreement count = `n − hammingDist`.** The number of block coordinates on which `f`
and `c` *agree* is `n − hammingDist f c`. Splits the universe of coordinates into the
agreeing and disagreeing parts. -/
lemma card_agree_eq (f c : ι → α) :
    (Finset.univ.filter (fun i => f i = c i)).card =
      Fintype.card ι - hammingDist f c := by
  simpa [Code.agreementCols] using
    Code.agreementCols_card_eq_card_sub_hammingDist (u := f) (v := c)

/-- **Real-valued disagreement bound from a relative-distance radius.** If the *real* relative
Hamming distance is bounded by `δ`, i.e. `(δᵣ(f, c) : ℝ) ≤ δ`, then the disagreement count is
bounded by `δ·n`:

  `(#{i : f i ≠ c i} : ℝ) ≤ δ · n`.

This unfolds `relHammingDist = hammingDist / n` and clears the (positive) denominator `n`. -/
lemma card_disagree_le_of_relHammingDist_le
    (f c : ι → α) {δ : ℝ}
    (hδ : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    ((Finset.univ.filter (fun i => f i ≠ c i)).card : ℝ) ≤ δ * Fintype.card ι := by
  classical
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `relHammingDist f c = hammingDist f c / n`, cast to ℝ.
  have hrel : ((Code.relHammingDist f c : ℚ≥0) : ℝ)
      = (hammingDist f c : ℝ) / Fintype.card ι := by
    rw [Code.relHammingDist]
    push_cast
    ring
  rw [hrel, div_le_iff₀ hn_pos] at hδ
  rw [hammingDist_eq_card_filter_ne] at hδ
  linarith

/-- **Agreement-coordinate lower bound (the greedy-chain step-1 datum).** For a codeword
`c ∈ closeCodewordsRel C f δ` (`c ∈ C` and `δᵣ(f, c) ≤ δ`), the number of block coordinates
on which `c` agrees with `f` is at least `(1 - δ)·n`:

  `(1 - δ) · n ≤ (#{i : f i = c i} : ℝ)`.

This is the per-element agreement bound that the CZ25 / Guruswami-Wang greedy chain consumes
in step 1 ("each candidate agrees with `f` on `≥ (τ(r₀)+η)·n` coordinates"): at the capacity
radius `δ = 1 - τ(r₀) - η`, the right-hand floor is `(τ(r₀)+η)·n`. Proven from the
relative-distance membership alone; no design / iterative-charge content. -/
lemma card_agree_ge_of_mem_closeCodewordsRel
    (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) := by
  classical
  rw [mem_closeCodewordsRel_iff_real] at hc
  have hdis := card_disagree_le_of_relHammingDist_le f c hc.2
  have hle : hammingDist f c ≤ Fintype.card ι := hammingDist_le_card_fintype
  -- `#agree = n - hammingDist`, cast to ℝ.
  have hagree : ((Finset.univ.filter (fun i => f i = c i)).card : ℝ)
      = (Fintype.card ι : ℝ) - hammingDist f c := by
    rw [card_agree_eq]
    push_cast [Nat.cast_sub hle]
    ring
  rw [hagree]
  rw [hammingDist_eq_card_filter_ne] at hle ⊢
  -- From `#disagree ≤ δ·n`, get `n - #disagree ≥ n - δ·n = (1-δ)·n`.
  nlinarith [hdis]

/-- **Double-counting / Fubini swap of the agreement table.** For a finite list `L` of
codewords, the total agreement mass — summed first over list elements `c ∈ L`, then over the
coordinates each agrees on — equals the same table summed coordinate-first:

  `∑_{c ∈ L} #{i : c i = f i} = ∑_{i} #{c ∈ L : c i = f i}`.

This swaps the order of the agreement double count. The right-hand side is exactly the
per-coordinate quantity `∑_i |{c ∈ L : c i = f i}|` that the CZ25 design half
(`sum_card_vanishing_le_design`) caps from above through the subspace-design budget; the
left-hand side is the per-element agreement the previous lemma lower-bounds. So this is the
bridge between the two halves of the dimension count. -/
lemma sum_agree_swap (f : ι → α) (L : Finset (ι → α)) :
    (∑ c ∈ L, (Finset.univ.filter (fun i => c i = f i)).card) =
      ∑ i : ι, (L.filter (fun c => c i = f i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Aggregate agreement lower bound over a list of close codewords.** If every codeword in
a finite list `L` lies in `closeCodewordsRel C f δ`, the total per-element agreement mass is
at least `|L| · (1 - δ) · n`:

  `|L| · (1 - δ) · n ≤ ∑_{c ∈ L} #{i : c i = f i}`.

Sums `card_agree_ge_of_mem_closeCodewordsRel` over the list. Combined with `sum_agree_swap`
this lower-bounds the coordinate-first agreement table `∑_i #{c ∈ L : c i = f i}` that the
design half caps — the elementary "fresh agreement mass" accounting feeding the greedy chain.
Note the order in the filter (`c i = f i`) matches `sum_agree_swap`; we use the symmetry of
equality to align with `card_agree_ge_of_mem_closeCodewordsRel`'s `f i = c i`. -/
lemma sum_agree_ge_of_subset_closeCodewordsRel
    (C : Set (ι → α)) (f : ι → α) {δ : ℝ}
    (L : Finset (ι → α)) (hL : ∀ c ∈ L, c ∈ closeCodewordsRel C f δ) :
    (L.card : ℝ) * ((1 - δ) * Fintype.card ι) ≤
      ∑ c ∈ L, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) := by
  classical
  have hper : ∀ c ∈ L, (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) := by
    intro c hc
    have h := card_agree_ge_of_mem_closeCodewordsRel C f c (hL c hc)
    -- align `f i = c i` (lemma) with `c i = f i` (here) via filter congruence.
    have hfilt : (Finset.univ.filter (fun i => f i = c i)).card
        = (Finset.univ.filter (fun i => c i = f i)).card := by
      simp only [eq_comm]
    rwa [hfilt] at h
  calc (L.card : ℝ) * ((1 - δ) * Fintype.card ι)
      = ∑ _c ∈ L, ((1 - δ) * Fintype.card ι) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ L, ((Finset.univ.filter (fun i => c i = f i)).card : ℝ) :=
        Finset.sum_le_sum hper

end AgreementCount

section DifferenceVanish

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- **Recentred-difference vanishing count (greedy-chain step-2 input).** If two codewords
`c` and `c₀` both lie in the close list around `f` at radius `δ`, then their recentred
difference vanishes on at least `(1 - 2δ)·n` block coordinates:

  `(1 - 2δ) · n ≤ #{i : c i - c₀ i = 0}`.

Indeed, `c` agrees with `f` on at least `(1 - δ)·n` coordinates and `c₀` agrees with `f` on
at least `(1 - δ)·n` coordinates. The intersection of the two agreement sets has size at
least `(1 - 2δ)·n`, and on that intersection `c i = f i = c₀ i`, so the recentred difference
vanishes. This is the reusable input that feeds the recentred span
`span {c - c₀ | c ∈ L}` into the subspace-design vanishing budget. -/
lemma card_diff_vanish_ge_of_mem_closeCodewordsRel
    (s : ℕ) (C : Set (ι → Fin s → F)) (f c c₀ : ι → Fin s → F) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ)
    (hc₀ : c₀ ∈ closeCodewordsRel C f δ) :
    (1 - 2 * δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ) := by
  classical
  let A : Finset ι := Finset.univ.filter (fun i => f i = c i)
  let B : Finset ι := Finset.univ.filter (fun i => f i = c₀ i)
  let V : Finset ι := Finset.univ.filter (fun i => c i - c₀ i = 0)
  have hA : (1 - δ) * Fintype.card ι ≤ (A.card : ℝ) := by
    simpa [A] using card_agree_ge_of_mem_closeCodewordsRel C f c hc
  have hB : (1 - δ) * Fintype.card ι ≤ (B.card : ℝ) := by
    simpa [B] using card_agree_ge_of_mem_closeCodewordsRel C f c₀ hc₀
  have hUnion : (((A ∪ B).card : ℕ) : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ (A ∪ B)
  have hInterEqNat : (A ∩ B).card = A.card + B.card - (A ∪ B).card := by
    have h := Finset.card_union_add_card_inter A B
    omega
  have hUnionLe : (A ∪ B).card ≤ A.card + B.card := by
    have h := Finset.card_union_add_card_inter A B
    omega
  have hInterEq : ((A ∩ B).card : ℝ) =
      (A.card : ℝ) + (B.card : ℝ) - ((A ∪ B).card : ℝ) := by
    rw [hInterEqNat, Nat.cast_sub hUnionLe]
    push_cast
    ring_nf
  have hInterLower : (1 - 2 * δ) * Fintype.card ι ≤ ((A ∩ B).card : ℝ) := by
    nlinarith [hA, hB, hUnion, hInterEq]
  have hsub : A ∩ B ⊆ V := by
    intro i hi
    simp [A, B, V] at hi ⊢
    rcases hi with ⟨hfi, hfi₀⟩
    have hcc : c i = c₀ i := by
      rw [← hfi, ← hfi₀]
    simp [hcc]
  have hcard : ((A ∩ B).card : ℝ) ≤ (V.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hInterLower hcard

/-- **Double-counting / Fubini swap for recentred vanishing.** For a finite list `L`, the
total number of coordinates where each recentred difference `c - c₀` vanishes can be summed
element-first or coordinate-first:

  `∑_{c ∈ L} #{i : c i - c₀ i = 0} = ∑_i #{c ∈ L : c i - c₀ i = 0}`.

The coordinate-first side is the table shape that the subspace-design vanishing budget acts
on after the list is recentred around `c₀`. -/
lemma sum_diff_vanish_swap
    (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) :
    (∑ c ∈ L, (Finset.univ.filter (fun i => c i - c₀ i = 0)).card) =
      ∑ i : ι, (L.filter (fun c => c i - c₀ i = 0)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Aggregate recentred-vanishing lower bound.** If `c₀` is close to `f` and every
`c ∈ L` is close to `f` at the same radius `δ`, summing
`card_diff_vanish_ge_of_mem_closeCodewordsRel` over `L` gives

  `|L| · (1 - 2δ) · n ≤ ∑_{c ∈ L} #{i : c i - c₀ i = 0}`.

This is the list-level form of the recentred-difference step. -/
lemma sum_diff_vanish_ge_of_subset_closeCodewordsRel
    (s : ℕ) (C : Set (ι → Fin s → F)) (f c₀ : ι → Fin s → F) {δ : ℝ}
    (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel C f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel C f δ) :
    (L.card : ℝ) * ((1 - 2 * δ) * Fintype.card ι) ≤
      ∑ c ∈ L, ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ) := by
  classical
  have hper : ∀ c ∈ L, (1 - 2 * δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ) := by
    intro c hc
    exact card_diff_vanish_ge_of_mem_closeCodewordsRel s C f c c₀ (hL c hc) hc₀
  calc (L.card : ℝ) * ((1 - 2 * δ) * Fintype.card ι)
      = ∑ _c ∈ L, ((1 - 2 * δ) * Fintype.card ι) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ L, ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ) :=
        Finset.sum_le_sum hper

/-- **Coordinate-first aggregate recentred-vanishing lower bound.** Combining the aggregate
recentred-vanishing lower bound with `sum_diff_vanish_swap`, the lower bound is exposed in
the coordinate-first table form:

  `|L| · (1 - 2δ) · n ≤ ∑_i #{c ∈ L : c i - c₀ i = 0}`.

This is the exact finite-table shape needed before translating vanishing fibers into the
recentred span and applying the subspace-design budget. -/
lemma sum_coord_diff_vanish_ge_of_subset_closeCodewordsRel
    (s : ℕ) (C : Set (ι → Fin s → F)) (f c₀ : ι → Fin s → F) {δ : ℝ}
    (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel C f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel C f δ) :
    (L.card : ℝ) * ((1 - 2 * δ) * Fintype.card ι) ≤
      ∑ i : ι, ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ) := by
  classical
  have hsum := sum_diff_vanish_ge_of_subset_closeCodewordsRel s C f c₀ L hc₀ hL
  have hswap : (∑ c ∈ L,
      ((Finset.univ.filter (fun i => c i - c₀ i = 0)).card : ℝ)) =
      ∑ i : ι, ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ) := by
    exact_mod_cast sum_diff_vanish_swap s c₀ L
  simpa [hswap] using hsum

end DifferenceVanish

section RecentredSpan

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- **A recentred difference is in the finite recentred span.** If `c ∈ L`, then
`c - c₀` belongs to the span of all recentred differences `{c - c₀ | c ∈ L}`. This is the
local span-membership fact used before intersecting with a coordinate kernel. -/
lemma diff_mem_span_diffs_of_mem
    (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F))
    {c : ι → Fin s → F} (hc : c ∈ L) :
    c - c₀ ∈
      Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) := by
  exact Submodule.subset_span (Set.mem_image_of_mem (fun c => c - c₀) hc)

/-- **A vanishing recentred difference lies in the coordinate kernel.** If the recentred
difference `c - c₀` vanishes at block coordinate `i`, then it lies in the kernel of the
coordinate projection `eval_i`. This is the local kernel-membership half of the
recentred-span/design bridge. -/
lemma diff_mem_ker_proj_of_vanish
    (s : ℕ) (c c₀ : ι → Fin s → F) (i : ι)
    (hzero : c i - c₀ i = 0) :
    c - c₀ ∈
      (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Submodule F (ι → Fin s → F)) := by
  simp [LinearMap.mem_ker, LinearMap.proj_apply, hzero]

/-- **Filtered recentred differences land in span ∩ kernel.** If `c` lies in the finite list
`L` and its recentred difference vanishes at coordinate `i`, then `c - c₀` is simultaneously
in the recentred span and in `ker(eval_i)`. This is the pointwise bridge between the finite
vanishing table and the subspace-design kernel intersection. -/
lemma diff_mem_span_diffs_inf_ker_of_mem_filter
    (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) (i : ι)
    {c : ι → Fin s → F} (hc : c ∈ L.filter (fun c => c i - c₀ i = 0)) :
    c - c₀ ∈
      (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Submodule F (ι → Fin s → F)) := by
  rw [Finset.mem_filter] at hc
  exact Submodule.mem_inf.mpr
    ⟨diff_mem_span_diffs_of_mem s c₀ L hc.1,
      diff_mem_ker_proj_of_vanish s c c₀ i hc.2⟩

/-- **The filtered-difference span is below the recentred span ∩ coordinate kernel.** The
span generated by differences from the coordinate-`i` vanishing fiber
`{c ∈ L | c i - c₀ i = 0}` is a subspace of
`span{c - c₀ | c ∈ L} ⊓ ker(eval_i)`.

This packages the local membership bridge in the exact submodule-inclusion form needed before
choosing an independent family and applying `sum_card_vanishing_le_design`. It does not assert
any cardinality or affine-flat bound. -/
lemma span_filter_diffs_le_span_diffs_inf_ker
    (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) (i : ι) :
    Submodule.span F
        ((fun c => c - c₀) ''
          ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F))) ≤
      (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Submodule F (ι → Fin s → F)) := by
  rw [Submodule.span_le]
  rintro x ⟨c, hc, rfl⟩
  exact diff_mem_span_diffs_inf_ker_of_mem_filter s c₀ L i hc

/-- **Linear-independent filtered fibers give the cardinality-to-dimension cap.** If the
recentred differences from one coordinate-vanishing fiber are linearly independent, then the
fiber cardinality is bounded by the dimension of its filtered-difference span.

This is the direct `finrank_span_eq_card` specialization for the hypothesis `hfiber` in
`list_vanish_mass_le_design_of_filter_card_le_finrank`. It does not prove the hard
Guruswami-Wang / affine-fiber argument that supplies the independence. -/
lemma filter_card_le_finrank_span_filter_diffs_of_linearIndependent
    (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) (i : ι)
    (hlin : LinearIndependent F
      (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀)) :
    ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ) ≤
      (Module.finrank F
        (Submodule.span F
          ((fun c => c - c₀) ''
            ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ) := by
  classical
  have hrange :
      Set.range (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀) =
        ((fun c => c - c₀) ''
          ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F))) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.1, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  have hfin :
      Module.finrank F
          (Submodule.span F
            ((fun c => c - c₀) ''
              ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) =
        (L.filter (fun c => c i - c₀ i = 0)).card := by
    rw [← hrange, finrank_span_eq_card hlin]
    simp
  exact_mod_cast hfin.ge

/-- **Recentred differences stay in the code submodule.** If `c` and `c₀` are both codewords
in the close list around `f`, then the difference `c - c₀` lies in the submodule code `C`.
This is the closure fact used when forming the recentred span
`span {c - c₀ | c ∈ L}` before applying the subspace-design budget. -/
lemma diff_mem_of_mem_closeCodewordsRel
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) (f c c₀ : ι → Fin s → F) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ) :
    c - c₀ ∈ C := by
  rw [mem_closeCodewordsRel_iff_real] at hc hc₀
  exact C.sub_mem hc.1 hc₀.1

/-- **The finite recentred span is a subspace of the code.** If `c₀` and every `c ∈ L` are
close codewords for a submodule code `C`, then the span of the recentred differences
`{c - c₀ | c ∈ L}` lies below `C`. This is the submodule-closure setup needed before
choosing a basis and feeding the recentred family to `sum_card_vanishing_le_design`. -/
lemma span_diffs_le_of_subset_closeCodewordsRel
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) (f c₀ : ι → Fin s → F) {δ : ℝ}
    (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ) :
    Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) ≤ C := by
  rw [Submodule.span_le]
  rintro x ⟨c, hcL, rfl⟩
  exact diff_mem_of_mem_closeCodewordsRel s C f c c₀ (hL c hcL) hc₀

/-- **Filtered recentred differences land in the code ∩ coordinate kernel.** If `c₀` and
every `c ∈ L` are close codewords for a submodule code `C`, then the span generated by the
coordinate-`i` vanishing filtered differences is a subspace of `C ⊓ ker(eval_i)`.

This is the close-codeword version of `span_filter_diffs_le_span_diffs_inf_ker`: it composes
the local span/ker bridge with `span_diffs_le_of_subset_closeCodewordsRel`, so downstream
design-half arguments can work directly inside the code's coordinate kernel intersection. -/
lemma span_filter_diffs_le_code_inf_ker_of_subset_closeCodewordsRel
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) (f c₀ : ι → Fin s → F) {δ : ℝ}
    (L : Finset (ι → Fin s → F)) (i : ι)
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ) :
    Submodule.span F
        ((fun c => c - c₀) ''
          ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F))) ≤
      (C ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Submodule F (ι → Fin s → F)) := by
  have hfilter := span_filter_diffs_le_span_diffs_inf_ker s c₀ L i
  have hspanC := span_diffs_le_of_subset_closeCodewordsRel s C f c₀ L hc₀ hL
  intro x hx
  have hxfilter := Submodule.mem_inf.mp (hfilter hx)
  exact Submodule.mem_inf.mpr ⟨hspanC hxfilter.1, hxfilter.2⟩

/-- **Filtered recentred span dimensions obey the subspace-design budget.** If `c₀` and
every `c ∈ L` are close codewords for a τ-subspace-design code `C`, and the full recentred
span has dimension at most `r₀`, then the sum over coordinates of the dimensions of the
coordinate-vanishing filtered-difference spans is bounded by the design budget for the full
recentred span:

`∑ i, dim span{c - c₀ | c ∈ L, c i - c₀ i = 0}
  ≤ dim span{c - c₀ | c ∈ L} · τ r₀ · n`.

This is still dimension-level bookkeeping; it does not assert that the filtered fiber
cardinalities are bounded by those dimensions. That missing affine-fiber/cardinality step is
the hard `CZ25CoordFiberCap` / Guruswami-Wang charge. -/
lemma sum_finrank_span_filter_diffs_le_design_of_subset_closeCodewordsRel
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀) :
    (∑ i : ι,
        (Module.finrank F
          (Submodule.span F
            ((fun c => c - c₀) ''
              ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ)) ≤
      (Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀ * Fintype.card ι := by
  classical
  set A : Submodule F (ι → Fin s → F) :=
    Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) with hA
  have hA_le : A ≤ C := by
    rw [hA]
    exact span_diffs_le_of_subset_closeCodewordsRel s C f c₀ L hc₀ hL
  have hper : ∀ i : ι,
      (Module.finrank F
        (Submodule.span F
          ((fun c => c - c₀) ''
            ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ) ≤
        (Module.finrank F
          (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ) := by
    intro i
    have hnat := Submodule.finrank_mono
      (span_filter_diffs_le_span_diffs_inf_ker s c₀ L i)
    rw [← hA] at hnat
    exact_mod_cast hnat
  have hsum_le :
      (∑ i : ι,
          (Module.finrank F
            (Submodule.span F
              ((fun c => c - c₀) ''
                ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ)) ≤
        ∑ i : ι,
          (Module.finrank F
            (↥(A ⊓
              (LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F))) : ℝ) :=
    Finset.sum_le_sum (fun i _ => hper i)
  have hdesign := h r₀ A hA_le (by simpa [hA] using hrank)
  have hn_posR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn_posR] at hdesign
  refine le_trans hsum_le ?_
  simpa [hA, mul_assoc] using hdesign

/-- **Conditional mass-charge bridge.** If, in addition to the design-budget hypotheses, every
coordinate fiber has cardinality bounded by the dimension of its filtered recentred-difference
span, then the total recentred-vanishing mass is bounded by the subspace-design budget for the
full recentred span:

`|L| * (1 - 2δ) * n ≤ dim span{c - c₀ | c ∈ L} * τ r₀ * n`.

This theorem deliberately keeps the per-coordinate fiber/cardinality cap as an explicit
hypothesis. That cap is the hard affine-fiber / Guruswami-Wang charge; this lemma only packages
the already-proved lower vanishing count and design-budget upper bound around it. -/
lemma list_vanish_mass_le_design_of_filter_card_le_finrank
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀)
    (hfiber : ∀ i : ι,
      ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ) ≤
        (Module.finrank F
          (Submodule.span F
            ((fun c => c - c₀) ''
              ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ)) :
    (L.card : ℝ) * ((1 - 2 * δ) * Fintype.card ι) ≤
      (Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀ * Fintype.card ι := by
  classical
  have hlower :=
    sum_coord_diff_vanish_ge_of_subset_closeCodewordsRel s ((C : Set (ι → Fin s → F)))
      f c₀ L hc₀ hL
  have hcard_to_dim :
      (∑ i : ι, ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ)) ≤
        ∑ i : ι,
          (Module.finrank F
            (Submodule.span F
              ((fun c => c - c₀) ''
                ((L.filter (fun c => c i - c₀ i = 0)) : Set (ι → Fin s → F)))) : ℝ) :=
    Finset.sum_le_sum (fun i _ => hfiber i)
  have hdesign :=
    sum_finrank_span_filter_diffs_le_design_of_subset_closeCodewordsRel
      s τ C h r₀ f c₀ L hc₀ hL hrank
  exact le_trans hlower (le_trans hcard_to_dim hdesign)

/-- **Mass-charge bridge from linear-independent fibers.** If each coordinate-vanishing
recentred fiber has linearly independent recentred differences, then its cardinality is bounded
by the dimension of its filtered-difference span, so the conditional mass-charge bridge applies.

This packages the already-proved per-coordinate `finrank_span_eq_card` specialization into the
design-budget theorem. It still keeps the hard Guruswami-Wang / affine-fiber argument as the
explicit linear-independence hypothesis. -/
lemma list_vanish_mass_le_design_of_filter_linearIndependent
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀)
    (hlin : ∀ i : ι, LinearIndependent F
      (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀)) :
    (L.card : ℝ) * ((1 - 2 * δ) * Fintype.card ι) ≤
      (Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀ * Fintype.card ι := by
  exact list_vanish_mass_le_design_of_filter_card_le_finrank
    s τ C h r₀ f c₀ L hc₀ hL hrank
    (fun i => filter_card_le_finrank_span_filter_diffs_of_linearIndependent s c₀ L i (hlin i))

/-- **Coordinate-count-cancelled linear-independent mass charge.** The finite coordinate count is
positive, so the linear-independent mass-charge inequality can be divided by the block length:

`|L| * (1 - 2δ) ≤ dim span{c - c₀ | c ∈ L} * τ r₀`.

This is only algebraic packaging around the design-budget bridge; the affine-fiber /
Guruswami-Wang content remains the explicit per-coordinate linear-independence hypothesis. -/
lemma list_card_mul_one_sub_two_delta_le_design_of_filter_linearIndependent
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀)
    (hlin : ∀ i : ι, LinearIndependent F
      (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀)) :
    (L.card : ℝ) * (1 - 2 * δ) ≤
      (Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀ := by
  have hmass := list_vanish_mass_le_design_of_filter_linearIndependent
    s τ C h r₀ f c₀ L hc₀ hL hrank hlin
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact (mul_le_mul_iff_left₀ hn_pos).mp (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmass)

/-- **Direct list-cardinality bound from linear-independent fibers.** If the CZ25 gap
`1 - 2δ` is positive, the coordinate-count-cancelled mass-charge inequality gives the direct
bound

`|L| ≤ (dim span{c - c₀ | c ∈ L} * τ r₀) / (1 - 2δ)`.

This is still algebraic packaging; the only non-bookkeeping hypothesis beyond the design setup is
the per-coordinate linear independence of the recentred vanishing fibers. -/
lemma list_card_le_design_div_gap_of_filter_linearIndependent
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hgap : 0 < 1 - 2 * δ)
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀)
    (hlin : ∀ i : ι, LinearIndependent F
      (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀)) :
    (L.card : ℝ) ≤
      ((Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀) / (1 - 2 * δ) := by
  rw [le_div_iff₀ hgap]
  exact list_card_mul_one_sub_two_delta_le_design_of_filter_linearIndependent
    s τ C h r₀ f c₀ L hc₀ hL hrank hlin

/-- **Rank-budget list-cardinality bound from linear-independent fibers.** Combining the direct
gap-division bound with the recentred-span rank cap gives the budget-only numerator
`r₀ * τ r₀`, assuming the design budget factor is nonnegative:

`|L| ≤ (r₀ * τ r₀) / (1 - 2δ)`.

This is the algebraic endpoint of the current reusable CZ25 dimension-count chain. The hard
content remains supplying the per-coordinate linear independence and CZ25 parameter choices. -/
lemma list_card_le_rank_budget_div_gap_of_filter_linearIndependent
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (r₀ : ℕ) (f c₀ : ι → Fin s → F) {δ : ℝ} (L : Finset (ι → Fin s → F))
    (hgap : 0 < 1 - 2 * δ) (hτ : 0 ≤ τ r₀)
    (hc₀ : c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hL : ∀ c ∈ L, c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ)
    (hrank :
      Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) ≤ r₀)
    (hlin : ∀ i : ι, LinearIndependent F
      (fun c : {c // c ∈ L.filter (fun c => c i - c₀ i = 0)} => c.1 - c₀)) :
    (L.card : ℝ) ≤ ((r₀ : ℝ) * τ r₀) / (1 - 2 * δ) := by
  have hcard := list_card_le_design_div_gap_of_filter_linearIndependent
    s τ C h r₀ f c₀ L hgap hc₀ hL hrank hlin
  have hfin :
      (Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) ≤
        r₀ := by
    exact_mod_cast hrank
  have hnum :
      ((Module.finrank F
          (Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))) : ℝ) *
        τ r₀) ≤ (r₀ : ℝ) * τ r₀ :=
    mul_le_mul_of_nonneg_right hfin hτ
  exact le_trans hcard (div_le_div_of_nonneg_right hnum hgap.le)

end RecentredSpan

section FiberRecentre

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- **Agreement fiber = recentred vanishing fiber, when the base agrees at `i`.** Fix a
coordinate `i` and a base word `c₀` that agrees with `f` at `i` (`c₀ i = f i`). Then for any
finite list `L`, the agreement fiber `{c ∈ L : c i = f i}` is *equal as a Finset* to the
recentred vanishing fiber `{c ∈ L : c i - c₀ i = 0}`:

  `L.filter (fun c => c i = f i) = L.filter (fun c => c i - c₀ i = 0)`.

Indeed, since `c₀ i = f i`, the predicate `c i = f i` is equivalent to `c i = c₀ i`, i.e. to
`c i - c₀ i = 0` (`sub_eq_zero`). This is the coordinate-recentring step of the CZ25 / GW
dimension count: it rewrites each per-coordinate term of the agreement table `coordAgreeSum`
(the LHS of `CZ25CoordFiberCap`) into the recentred vanishing-fiber form that the design half
acts on, so the already-landed span/kernel bricks
(`span_filter_diffs_le_code_inf_ker_of_subset_closeCodewordsRel`) and the design budget
(`sum_card_vanishing_le_design`) apply directly. It does **not** prove any cardinality cap —
in particular not the affine-flat `CZ25CoordFiberCap` (the `q^{dim}` vs `dim+1` GW charge
documented in `CZ25SpanDimension.lean:292-302`); it is purely the recentring identity. -/
lemma filter_agree_eq_filter_vanish_of_base
    (s : ℕ) (f c₀ : ι → Fin s → F) (i : ι) (L : Finset (ι → Fin s → F))
    (hbase : c₀ i = f i) :
    L.filter (fun c => c i = f i) = L.filter (fun c => c i - c₀ i = 0) := by
  apply Finset.filter_congr
  intro c _hc
  rw [sub_eq_zero, hbase]

/-- **Cardinality form of the agreement↔recentred-vanishing fiber identity.** Immediate
corollary of `filter_agree_eq_filter_vanish_of_base`: when the base `c₀` agrees with `f` at
coordinate `i`, the agreement-fiber count equals the recentred vanishing-fiber count,

  `#{c ∈ L : c i = f i} = #{c ∈ L : c i - c₀ i = 0}`.

This is the table-entry rewrite used to pass from the coordinate agreement table
`coordAgreeSum` (lower-bounded by `sum_agree_ge_of_subset_closeCodewordsRel`) to the recentred
vanishing table the design budget caps. -/
lemma card_filter_agree_eq_card_filter_vanish_of_base
    (s : ℕ) (f c₀ : ι → Fin s → F) (i : ι) (L : Finset (ι → Fin s → F))
    (hbase : c₀ i = f i) :
    (L.filter (fun c => c i = f i)).card
      = (L.filter (fun c => c i - c₀ i = 0)).card := by
  rw [filter_agree_eq_filter_vanish_of_base s f c₀ i L hbase]

/-- **Aggregate agreement↔vanishing rewrite on the base-agreement coordinates.** Summing over
the coordinates where `c₀` agrees with `f`, the agreement-fiber table has the same real-valued
mass as the recentred vanishing-fiber table:

`∑_{i : c₀ i = f i} |{c ∈ L | c i = f i}|
  = ∑_{i : c₀ i = f i} |{c ∈ L | c i - c₀ i = 0}|`.

This is the finite-table form of `card_filter_agree_eq_card_filter_vanish_of_base` used when
moving from agreement-count lower bounds to recentred-vanishing design-budget terms. -/
lemma sum_card_filter_agree_eq_sum_card_filter_vanish_on_base_agreement
    (s : ℕ) (f c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) :
    (∑ i ∈ Finset.univ.filter (fun i => c₀ i = f i),
        ((L.filter (fun c => c i = f i)).card : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i => c₀ i = f i),
        ((L.filter (fun c => c i - c₀ i = 0)).card : ℝ) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact_mod_cast card_filter_agree_eq_card_filter_vanish_of_base
    s f c₀ i L (Finset.mem_filter.mp hi).2

end FiberRecentre

/-! ### `#print axioms` verification anchors -/

section AxiomCheck

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

example (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card :=
  hammingDist_eq_card_filter_ne f c

example (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) :=
  card_agree_ge_of_mem_closeCodewordsRel C f c hc

example (f : ι → α) (L : Finset (ι → α)) :
    (∑ c ∈ L, (Finset.univ.filter (fun i => c i = f i)).card) =
      ∑ i : ι, (L.filter (fun c => c i = f i)).card :=
  sum_agree_swap f L

end AxiomCheck

end CodingTheory

#print axioms CodingTheory.hammingDist_eq_card_filter_ne
#print axioms CodingTheory.card_agree_eq
#print axioms CodingTheory.card_disagree_le_of_relHammingDist_le
#print axioms CodingTheory.card_agree_ge_of_mem_closeCodewordsRel
#print axioms CodingTheory.sum_agree_swap
#print axioms CodingTheory.sum_agree_ge_of_subset_closeCodewordsRel
#print axioms CodingTheory.card_diff_vanish_ge_of_mem_closeCodewordsRel
#print axioms CodingTheory.sum_diff_vanish_swap
#print axioms CodingTheory.sum_diff_vanish_ge_of_subset_closeCodewordsRel
#print axioms CodingTheory.sum_coord_diff_vanish_ge_of_subset_closeCodewordsRel
#print axioms CodingTheory.diff_mem_span_diffs_of_mem
#print axioms CodingTheory.diff_mem_ker_proj_of_vanish
#print axioms CodingTheory.diff_mem_span_diffs_inf_ker_of_mem_filter
#print axioms CodingTheory.span_filter_diffs_le_span_diffs_inf_ker
#print axioms CodingTheory.filter_card_le_finrank_span_filter_diffs_of_linearIndependent
#print axioms CodingTheory.diff_mem_of_mem_closeCodewordsRel
#print axioms CodingTheory.span_diffs_le_of_subset_closeCodewordsRel
#print axioms CodingTheory.span_filter_diffs_le_code_inf_ker_of_subset_closeCodewordsRel
#print axioms CodingTheory.sum_finrank_span_filter_diffs_le_design_of_subset_closeCodewordsRel
#print axioms CodingTheory.list_vanish_mass_le_design_of_filter_card_le_finrank
#print axioms CodingTheory.list_vanish_mass_le_design_of_filter_linearIndependent
#print axioms CodingTheory.list_card_mul_one_sub_two_delta_le_design_of_filter_linearIndependent
#print axioms CodingTheory.list_card_le_design_div_gap_of_filter_linearIndependent
#print axioms CodingTheory.list_card_le_rank_budget_div_gap_of_filter_linearIndependent
#print axioms CodingTheory.filter_agree_eq_filter_vanish_of_base
#print axioms CodingTheory.card_filter_agree_eq_card_filter_vanish_of_base
#print axioms CodingTheory.sum_card_filter_agree_eq_sum_card_filter_vanish_on_base_agreement
