/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson

/-!
# The Hab25 dichotomy bundle — the residual shape the paper actually constructs

`Hab25JohnsonAlgebraicData` demands a per-factor affine pair (`d₀`, `d₁`, `hImprove`) for
**every** factor covering the mutual disagreement set.  But [Hab25] Claim 1 is a *dichotomy
by contradiction*: the useful-factor machinery (Hensel lift, unique affine pair) fires only
for factors whose exceptional set **exceeds** the threshold `2·D_Y²·D_X·D_{YZ}`; for factors
below the threshold no pair is produced — the factor is counted by the threshold itself.
A faithful transcription of the paper therefore lands in the weaker bundle defined here:
per factor, *either* a threshold bound *or* an affine pair with the improvement property.

This file provides that bundle and proves its counting theorem from the in-tree integer
endgame (`factorImprove_card_le_n`, S7–S8, proven): the disagreement set has at most
`ℓ · max T n` elements.  The original every-factor bundle embeds via `T = 0`
(`Hab25JohnsonAlgebraicData.toDichotomy`), recovering the stronger `ℓ·n` bound; the
paper's Theorem 2 regime (`T = (ℓ⁶/3)(ρn)² ≥ n`) gives `ℓ·T`, matching [Hab25]'s
`(ℓ⁷/3)(ρn)²` form.

Constructing a `Hab25JohnsonDichotomyData` instance from the GS interpolation over `F(Z)`
(the L2–L5 chain of the roadmap) is the remaining open program; this file ensures that
program targets the bundle shape the paper can actually fill.

## Main results

* `Hab25JohnsonDichotomyData` — the dichotomy-shaped residual bundle.
* `Hab25JohnsonDichotomyData.disagree_card_le` — `|E| ≤ ℓ · max T n`, proven.
* `Hab25JohnsonDichotomyData.disagree_card_le_of_n_le` — the paper regime `|E| ≤ ℓ·T`.
* `Hab25JohnsonAlgebraicData.toDichotomy` — the every-factor bundle is the `T = 0` case.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654 (§5, whose Steps 5–7 + Appendix C produce the affine pair only
  above the Claim 5.7 threshold).
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The Hab25 dichotomy bundle.**  Per factor, either the exceptional set is bounded by
the threshold `T` (the below-threshold branch of [Hab25] Claim 1, where no affine pair is
produced), or an affine pair exists with the improvement property (the useful-factor
branch).  This is the residual shape a faithful transcription of the paper fills; the
every-factor bundle `Hab25JohnsonAlgebraicData` is the special case `T = 0`. -/
structure Hab25JohnsonDichotomyData
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) where
  /-- factor index type -/
  Idx : Type
  /-- decidable equality for the index type -/
  decIdx : DecidableEq Idx
  /-- the finite set of irreducible-factor indices -/
  Index : Finset Idx
  /-- the list-size bound (`D_Y < ℓ`) -/
  ℓ : ℕ
  /-- the per-factor threshold (`2·D_Y²·D_X·D_{YZ}` in [BCIKS20] Claim 5.7) -/
  T : ℕ
  /-- S3: the factor count is bounded by the list size -/
  hYbound : Index.card ≤ ℓ
  /-- the mutual disagreement set of exceptional scalars -/
  Edis : Finset F₀
  /-- the per-factor exceptional-scalar sets -/
  Efactor : Idx → Finset F₀
  /-- S4: the cover `E ⊆ ⋃ E_{i,j}` -/
  hcover : Edis ⊆ Index.biUnion Efactor
  /-- **The dichotomy** ([Hab25] Claim 1): each factor is small, or it admits an affine
  pair such that every exceptional scalar improves agreement at a disagreement point. -/
  hdichotomy : ∀ ij ∈ Index,
    (Efactor ij).card ≤ T ∨
    ∃ d₀ d₁ : ι₀ → F₀, ∀ z ∈ Efactor ij,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0

namespace Hab25JohnsonDichotomyData

variable {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
  {hη : 0 < η} {hδ : InJohnsonRange domain k η δ}

/-- **The dichotomy counting theorem (proven).**  Every factor contributes at most
`max T n` exceptional scalars — the small branch by hypothesis, the useful branch by the
proven improvement count `factorImprove_card_le_n` — so the union has at most
`ℓ · max T n`. -/
theorem disagree_card_le (A : Hab25JohnsonDichotomyData domain k η δ hη hδ) :
    A.Edis.card ≤ A.ℓ * max A.T (Fintype.card ι₀) := by
  letI := A.decIdx
  calc A.Edis.card
      ≤ (A.Index.biUnion A.Efactor).card := Finset.card_le_card A.hcover
    _ ≤ ∑ ij ∈ A.Index, (A.Efactor ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ A.Index, max A.T (Fintype.card ι₀) := by
        refine Finset.sum_le_sum fun ij hij => ?_
        rcases A.hdichotomy ij hij with h | ⟨d₀, d₁, h⟩
        · exact le_trans h (le_max_left _ _)
        · exact le_trans (factorImprove_card_le_n d₀ d₁ (A.Efactor ij) h)
            (le_max_right _ _)
    _ = A.Index.card * max A.T (Fintype.card ι₀) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ A.ℓ * max A.T (Fintype.card ι₀) :=
        Nat.mul_le_mul_right _ A.hYbound

/-- **The paper regime.**  When the threshold dominates the block length (as in [Hab25]
Theorem 2, where `T = (ℓ⁶/3)(ρn)² ≥ n`), the count is `ℓ·T` — the `(ℓ⁷/3)(ρn)²` form. -/
theorem disagree_card_le_of_n_le (A : Hab25JohnsonDichotomyData domain k η δ hη hδ)
    (hT : Fintype.card ι₀ ≤ A.T) :
    A.Edis.card ≤ A.ℓ * A.T := by
  have h := A.disagree_card_le
  rwa [max_eq_left hT] at h

end Hab25JohnsonDichotomyData

/-- The every-factor bundle is the `T = 0` case of the dichotomy bundle: each factor
takes the useful branch. -/
def Hab25JohnsonAlgebraicData.toDichotomy
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η} {hδ : InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ) :
    Hab25JohnsonDichotomyData domain k η δ hη hδ where
  Idx := A.Idx
  decIdx := A.decIdx
  Index := A.Index
  ℓ := A.ℓ
  T := 0
  hYbound := A.hYbound
  Edis := A.Edis
  Efactor := A.Efactor
  hcover := A.hcover
  hdichotomy := fun ij hij => Or.inr ⟨A.d₀ ij, A.d₁ ij, A.hImprove ij hij⟩

/-- Round-trip sanity: the `T = 0` embedding recovers the original `ℓ·n` bound. -/
theorem Hab25JohnsonAlgebraicData.toDichotomy_card
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η} {hδ : InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ) :
    A.Edis.card ≤ A.ℓ * Fintype.card ι₀ := by
  have h := A.toDichotomy.disagree_card_le
  simpa using h

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonDichotomyData.disagree_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonAlgebraicData.toDichotomy_card
