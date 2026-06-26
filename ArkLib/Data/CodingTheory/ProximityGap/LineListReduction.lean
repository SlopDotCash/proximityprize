/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CodewordHeavyScalar

/-!
# The line-list reduction: bad scalars ≤ (affine-line list size) · ⌊n/a⌋

Issue #389, the positive direction. The bipartite incidence skeleton
(`CodewordHeavyScalar.lean`: each codeword feeds `≤ ⌊n/a⌋` scalars; `LineCorePartition.lean`:
each core belongs to one scalar) yields a clean **reduction of the per-scalar MCA count to a
single line list size**:

> **`badScalar_card_le_lineList_mul`** — with `a = k+m+1` and nonvanishing direction `u₁`,
> the scalars `γ` for which some codeword agrees with `w_γ = u₀ + γ·u₁` on `≥ a` points
> number at most `Λ · ⌊n/a⌋`, where `Λ` is the **affine-line list size** — the number of
> codewords that come within agreement `a` of *some* word on the line.

This is structurally better than the per-word list-decoding the supply naively asks for: it
replaces the worst-case-over-`q`-words list size with **one** list — the codewords near the
whole affine line `{u₀ + γ·u₁}`. The wall now reads "bound `Λ` (the line list) sub-trivially";
`Λ ≤ q · (worst per-word list)` always, but `Λ` can be far smaller, and for `u₁ = xᵏ` far from
the code the line is a genuinely 1-parameter family whose list size is the natural object of
affine-subspace list decoding (Guruswami–Xing and successors). It is the cleanest positive-side
target the incidence skeleton produces.

## References

* Issue #389; `CodewordHeavyScalar.lean` (`codeword_heavy_scalar_card_le`),
  `LineCorePartition.lean`, `ExplainableCoreExactCount.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The scalars whose line word `u₀ + γ • u₁` is agreed with by some codeword on at least
`a` coordinates.  This is the line-list bad-scalar set used by
`badScalar_card_le_lineList_mul`. -/
noncomputable def lineBadScalars (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The codewords that appear somewhere along the affine line `u₀ + γ • u₁` with agreement
at least `a`.  Bounding this finite set is the line-list-size input left after the per-codeword
heavy-scalar bound. -/
noncomputable def lineAppearingCodewords (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

/-- A budgeted line list: at most `L` codewords appear with agreement `a` somewhere on the line. -/
def LineListBudgeted (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (L : ℕ) : Prop :=
  (lineAppearingCodewords dom k a u₀ u₁).card ≤ L

open Classical in
/-- **The line-list reduction.** With nonvanishing direction `u₁`, the scalars whose line
word `w_γ` is agreed with by some codeword on `≥ a` points are covered by the appearing
codewords, each contributing `≤ ⌊n/a⌋` of them: `#badScalars ≤ Λ · ⌊n/a⌋`. -/
theorem badScalar_card_le_lineList_mul (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    ((Finset.univ : Finset F).filter
        (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card
        * (n / a) := by
  classical
  set badΓ : Finset F := (Finset.univ : Finset F).filter
    (fun γ => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with hbadΓ
  set appC : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card) with happC
  -- bad scalars are covered by the per-codeword heavy-scalar sets of appearing codewords
  have hcover : badΓ ⊆ appC.biUnion (fun c =>
      (Finset.univ : Finset F).filter
        (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)) := by
    intro γ hγ
    obtain ⟨-, c, hc, hca⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_biUnion.mpr ⟨c, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, γ, hca⟩
  calc badΓ.card
      ≤ (appC.biUnion (fun c => (Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ c ∈ appC, ((Finset.univ : Finset F).filter
          (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ appC, (n / a) :=
        Finset.sum_le_sum fun c _ => codeword_heavy_scalar_card_le a ha c u₀ u₁ hu₁
    _ = appC.card * (n / a) := by rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Named-set form of `badScalar_card_le_lineList_mul`. -/
theorem lineBadScalars_card_le_lineAppearingCodewords_card_mul
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * (n / a) := by
  simpa [lineBadScalars, lineAppearingCodewords]
    using badScalar_card_le_lineList_mul dom k a ha u₀ u₁ hu₁

open Classical in
/-- Budgeted line-list consumer: if the line has at most `L` appearing codewords, then its
bad-scalar set is bounded by `L * ⌊n/a⌋`.  This isolates the remaining positive-side obligation
as a line-list-size theorem. -/
theorem lineBadScalars_card_le_of_lineListBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hL : LineListBudgeted dom k a u₀ u₁ L) :
    (lineBadScalars dom k a u₀ u₁).card ≤ L * (n / a) := by
  exact le_trans
    (lineBadScalars_card_le_lineAppearingCodewords_card_mul dom k a ha u₀ u₁ hu₁)
    (Nat.mul_le_mul_right (n / a) hL)

open Classical in
/-- Scanner-facing contrapositive: if a line has more bad scalars than `L * ⌊n/a⌋`, then the
line-list budget `L` is false.  The per-codeword ratio-census layer cannot be blamed; the
obstruction is an oversized appearing-codeword list. -/
theorem not_lineListBudgeted_of_lineBadScalars_card_gt
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hgt : L * (n / a) < (lineBadScalars dom k a u₀ u₁).card) :
    ¬ LineListBudgeted dom k a u₀ u₁ L := by
  intro hL
  exact (not_lt_of_ge
    (lineBadScalars_card_le_of_lineListBudgeted dom k a ha u₀ u₁ hu₁ hL)) hgt

open Classical in
/-- Equivalent numeric witness form of the previous theorem: an over-budget bad-scalar count
forces the appearing-codeword list itself to have more than `L` members. -/
theorem lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt
    (dom : Fin n ↪ F) (k a : ℕ) (ha : 1 ≤ a)
    (u₀ u₁ : Fin n → F) (hu₁ : ∀ i, u₁ i ≠ 0) {L : ℕ}
    (hgt : L * (n / a) < (lineBadScalars dom k a u₀ u₁).card) :
    L < (lineAppearingCodewords dom k a u₀ u₁).card := by
  exact lt_of_not_ge
    (not_lineListBudgeted_of_lineBadScalars_card_gt dom k a ha u₀ u₁ hu₁ hgt)

/-! ## Source audit -/

#print axioms badScalar_card_le_lineList_mul
#print axioms lineBadScalars_card_le_lineAppearingCodewords_card_mul
#print axioms lineBadScalars_card_le_of_lineListBudgeted
#print axioms not_lineListBudgeted_of_lineBadScalars_card_gt
#print axioms lineAppearingCodewords_card_gt_of_lineBadScalars_card_gt

end ProximityGap.Ownership
