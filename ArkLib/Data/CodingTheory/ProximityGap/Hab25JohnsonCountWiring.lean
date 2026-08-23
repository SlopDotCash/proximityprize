/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonDichotomy

/-!
# Count wiring for the Hab25 Johnson discharge

The numeric edge `JohnsonNumericBound` is a bound on `ε_mca`, which takes a supremum over
word pairs, while the (dichotomy) residual bundles count the exceptional scalars of a
*single* line.  This file supplies the missing semantic wiring between the two, so that the
entire below-Johnson program reduces to one named per-pair construction obligation:

* `badCount_le_of_dichotomy_cover` — if a dichotomy bundle's disagreement set covers the
  actual `mcaEvent`-bad scalars of a given pair, that pair's bad count is at most
  `ℓ · max T n` (via the proven `disagree_card_le`);
* `johnsonNumericBound_of_badCount_le` — a uniform per-pair bad-count bound `B` together
  with the arithmetic side condition `B/|F| ≤ johnsonBoundReal` discharges
  `JohnsonNumericBound` (via the in-tree keystone `epsMCA_le_of_badCount_le`);
* `johnsonNumericBound_of_forall_dichotomy` — **the named remaining obligation**: if every
  word pair admits a dichotomy bundle covering its bad scalars within a budget `B`
  satisfying the arithmetic side condition, the numeric edge holds.

After this file, discharging `JohnsonNumericBound` is exactly: *construct, for each word
pair, a `Hab25JohnsonDichotomyData` whose `Edis` covers the pair's `mcaEvent`-bad scalars,
with `ℓ · max T n` inside the Johnson budget* — the GS-over-`F(Z)` chain (S2–S8, in-tree)
modulo the single deep gap `hlin` ([BCIKS20] Claim 5.8/5.9).

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open _root_.ProximityGap Code
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

open Classical in
/-- **Per-pair semantic bridge.**  If a dichotomy bundle's disagreement set covers the
`mcaEvent`-bad scalars of the pair `u`, then `u`'s bad-scalar count is bounded by the
bundle's proven `ℓ · max T n` count. -/
theorem badCount_le_of_dichotomy_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η} {hδ : InJohnsonRange domain k η δ}
    (u : WordStack F₀ (Fin 2) ι₀)
    (A : Hab25JohnsonDichotomyData domain k η δ hη hδ)
    (hsem : Finset.univ.filter
        (fun γ : F₀ =>
          mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)
      ⊆ A.Edis) :
    (Finset.univ.filter
        (fun γ : F₀ =>
          mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)).card
      ≤ A.ℓ * max A.T (Fintype.card ι₀) :=
  le_trans (Finset.card_le_card hsem) A.disagree_card_le

open Classical in
/-- **Count form of the numeric edge.**  A uniform per-pair bad-count bound `B`, together
with the arithmetic side condition `B/|F| ≤ johnsonBoundReal`, discharges
`JohnsonNumericBound` via the in-tree keystone `epsMCA_le_of_badCount_le`. -/
theorem johnsonNumericBound_of_badCount_le
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (B : ℕ)
    (hcount : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.univ.filter
        (fun γ : F₀ =>
          mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)).card ≤ B)
    (harith : (B : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ := by
  unfold JohnsonNumericBound
  exact le_trans (epsMCA_le_of_badCount_le _ _ B hcount) harith

open Classical in
/-- **The named remaining obligation of the below-Johnson program.**  If every word pair
admits a dichotomy bundle covering its `mcaEvent`-bad scalars within a budget `B`
satisfying the Johnson arithmetic, the numeric edge holds.  After this theorem, the
entire [Hab25] discharge is the per-pair construction of such bundles from the
GS-over-`F(Z)` chain — the in-tree S2–S8 machinery modulo the single deep gap `hlin`
([BCIKS20] Claim 5.8/5.9). -/
theorem johnsonNumericBound_of_forall_dichotomy
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (B : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδ,
        (Finset.univ.filter
          (fun γ : F₀ =>
            mcaEvent (ReedSolomon.code domain k : Set (ι₀ → F₀)) δ (u 0) (u 1) γ)
          ⊆ A.Edis) ∧
        A.ℓ * max A.T (Fintype.card ι₀) ≤ B)
    (harith : (B : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ)) :
    JohnsonNumericBound domain k η δ := by
  refine johnsonNumericBound_of_badCount_le domain k η δ B (fun u => ?_) harith
  obtain ⟨A, hsem, hB⟩ := hdata u
  exact le_trans (badCount_le_of_dichotomy_cover u A hsem) hB

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_of_dichotomy_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_badCount_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_forall_dichotomy
