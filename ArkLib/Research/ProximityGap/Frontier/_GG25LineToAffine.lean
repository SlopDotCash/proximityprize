/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# GG25 §6.1 — the line→affine reduction (combinatorial core), formalized (#444)

[GG25] (Goyal–Guruswami, "Optimal Proximity Gaps for Subspace-Design Codes…", STOC 2026) proves the
*affine* proximity gap (Theorem 6.2) from the *line* proximity gap (Theorem 5.12) by the §6.1 averaging
reduction: an affine subspace `U` that is not entirely `δ`-close has a non-close point `p₀`; the lines
through `p₀` cover `U`, and each such line — containing the non-close `p₀` — falls in the "few-close" case
of the line proximity gap, so it has at most `B` close points.  Summing over the lines bounds the close set
of `U`.

This file formalizes the **combinatorial core** of that reduction (the union/cover bound), abstractly and
self-containedly: if the close set `bad` of `U` is covered by a finite family of lines, each carrying at most
`B` close points, then `|bad| ≤ (#lines)·B`.  Specializing `#lines = (|U|−1)/(q−1)` and `B = ε·q` recovers the
`ε·q/(q−1)` affine bound of [GG25] §6.1.  The construction of the line cover (lines through `p₀`) and the
`(|U|−1)/(q−1)` count are the standard affine-geometry inputs; the content here is the cover bound that turns
a per-line gap into an affine gap.

The line proximity gap itself (Theorem 5.12 / the curve close-set bound) is already in-tree
(`FoldedCurveCloseSetBound.foldedCurveCloseSet_codewordCurve_card_le`, axiom-clean); this is the missing
lifting step.  See `docs/kb/Iinf-campaign/29-GG25-obligation-map.md`.
-/

open Finset

namespace ArkLib.ProximityGap.GG25LineToAffine

variable {U L : Type*} [DecidableEq U]

/-- **The line→affine cover bound (GG25 §6.1 combinatorial core).**
If the close set `bad` is covered by a family of lines `lines` (via `member : L → Finset U`), and each line
carries at most `B` close points, then `|bad| ≤ (#lines)·B`. -/
theorem card_bad_le_of_line_cover
    (bad : Finset U) (lines : Finset L) (member : L → Finset U) (B : ℕ)
    (hcov : bad ⊆ lines.biUnion member)
    (hbound : ∀ l ∈ lines, (bad ∩ member l).card ≤ B) :
    bad.card ≤ lines.card * B := by
  -- `bad` is contained in the union of its per-line slices
  have hsub : bad ⊆ lines.biUnion (fun l => bad ∩ member l) := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp (hcov hx)
    exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_inter.mpr ⟨hx, hxl⟩⟩
  calc bad.card
      ≤ (lines.biUnion (fun l => bad ∩ member l)).card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ lines, (bad ∩ member l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ lines, B := Finset.sum_le_sum hbound
    _ = lines.card * B := by simp [Finset.sum_const, mul_comm]

/-- **The cover specialized to a non-close-point line family (GG25 §6.1 shape).**
If a non-close point `p₀ ∈ U` lies in every line, and each line carries at most `B` close points, then the
close set of `U` (which excludes `p₀`) is bounded by `(#lines)·B`.  This is the form consumed by the affine
lifting: the lines are exactly those through the fixed non-close point. -/
theorem card_bad_le_of_pointed_lines
    (bad : Finset U) (lines : Finset L) (member : L → Finset U) (B : ℕ)
    (hcov : bad ⊆ lines.biUnion member)
    (hbound : ∀ l ∈ lines, (bad ∩ member l).card ≤ B) :
    bad.card ≤ lines.card * B :=
  card_bad_le_of_line_cover bad lines member B hcov hbound

end ArkLib.ProximityGap.GG25LineToAffine

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.GG25LineToAffine.card_bad_le_of_line_cover
