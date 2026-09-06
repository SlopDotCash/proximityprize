/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodFromListSize

/-!
# Attack #05 — curve list-size for plain smooth RS reduces to the per-radius RS list size

This is the honest structural core of angle #05 (GG25 curve-decodability for plain smooth RS).
The GG25 engine `curveDecodable_of_curveListSize` (proven, axiom-clean) reduces δ* to the single
quantity `m` = number of distinct codeword-curves in a `CurveAssignment`'s image over the close
set. The open question is whether `m` for *plain* RS above Johnson is the generalized-Paley
eigenvalue (input 1) or a different object.

We pin it: a `CurveAssignment`'s `chooseCurve α` is, *row by row*, a tuple of codewords; the
distinct-curve count is bounded by the product over rows `j ≤ ℓ` of the number of distinct
codewords appearing in row `j`. That per-row count is exactly the **list-decoding list size of the
fixed code `C` at radius δ** (codewords close to the seed-data row). So:

  curve list-size  ≤  (∏ over rows) (per-row RS list size at radius δ).

Conclusion (the lever analysis, stated as a Lean fact below + the essay):
* The curve list-size is governed by the **RS list-decoding list size above Johnson**, NOT directly
  by `M = max|η_b|` (the Paley graph eigenvalue, input 1). It is the *hyperplane / line-ball*
  object (BCHKS Conj 1.12, input 2): bounding the per-row list size above Johnson for fixed RS is
  exactly the √q-cancellation line-ball incidence. So angle #05 does NOT bypass Paley — it routes
  to input (2), the same wall `_PrizeFloorOfBGK` already reduces to.
* The one genuinely-different lever — GG25's `field-size-linear-in-n` that makes `m = O(1/η)` for
  folded/random RS — is UNAVAILABLE for plain RS: it needs a fresh random row per seed, which plain
  fixed RS does not have. The prize regime `q ≈ n·2^128` is field-size *linear* in n, but the rows
  are the *fixed* RS code, not independent randomness, so the GG25 list-recovery argument does not
  fire. This is the exact step where the smooth-domain curve route reduces to the wall.
-/

open Finset Code
open scoped NNReal

set_option linter.unusedSectionVars false

namespace ProximityGap.Attack05

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The set of distinct codewords appearing in row `j` of a curve assignment over the close set.
This is a subset of `C` (each is a chosen codeword). Its cardinality is the per-row list size. -/
noncomputable def rowList (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A)
    (asgn : CurveAssignment C ℓ δ u f) (j : Fin (ℓ + 1)) : Finset (ι → A) :=
  (curveCloseSet δ u f).image (fun α => asgn.chooseCurve α j)

/-- **Per-row factorization of the curve list size.** The number of distinct *curves*
(`(ℓ+1)`-tuples of codewords) in the image is at most the product over rows of the per-row distinct
codeword counts. This is the structural identity that pins the curve list-size object: it is a
product of *list-decoding list sizes at radius δ*, one per row — NOT the Paley eigenvalue. -/
theorem curveListSize_le_prod_rowList (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (asgn : CurveAssignment C ℓ δ u f) :
    ((curveCloseSet δ u f).image asgn.chooseCurve).card
      ≤ ∏ j : Fin (ℓ + 1), (rowList C ℓ δ u f asgn j).card := by
  classical
  -- The map `cs ↦ (fun j => cs j)` embeds the curve-image into the product of the row-images.
  -- Each curve `asgn.chooseCurve α` lands in `∏ j, rowList … j` via its rows.
  set S := curveCloseSet δ u f
  -- Build an injection from the curve image into the dependent product of row lists.
  have hsub : (S.image asgn.chooseCurve) ⊆
      (Fintype.piFinset (fun j => rowList C ℓ δ u f asgn j)).image
        (fun (g : Fin (ℓ + 1) → ι → A) => g) := by
    intro cs hcs
    rw [Finset.mem_image] at hcs
    obtain ⟨α, hαS, rfl⟩ := hcs
    rw [Finset.mem_image]
    refine ⟨asgn.chooseCurve α, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hαS
  calc (S.image asgn.chooseCurve).card
      ≤ ((Fintype.piFinset (fun j => rowList C ℓ δ u f asgn j)).image
          (fun g : Fin (ℓ + 1) → ι → A => g)).card := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset (fun j => rowList C ℓ δ u f asgn j)).card := Finset.card_image_le
    _ = ∏ j : Fin (ℓ + 1), (rowList C ℓ δ u f asgn j).card := Fintype.card_piFinset _

/-- **The reduction, stated as a sufficient condition.** If every per-row list `rowList … j` has
size `≤ L` (the RS list-decoding list size at radius δ), then the curve list-size is `≤ L^(ℓ+1)`,
hence `CurveListSizeLe` holds with `m = L^(ℓ+1)` whenever every assignment achieves the per-row
bound. This makes the dependence on the **per-row list size** explicit: the curve route's only
open input is `L = ` RS list size above Johnson = the BCHKS line-ball object (input 2). -/
theorem curveListSize_le_pow_of_rowList_le (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0)
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) (asgn : CurveAssignment C ℓ δ u f) (L : ℕ)
    (hrow : ∀ j, (rowList C ℓ δ u f asgn j).card ≤ L) :
    ((curveCloseSet δ u f).image asgn.chooseCurve).card ≤ L ^ (ℓ + 1) := by
  classical
  refine le_trans (curveListSize_le_prod_rowList C ℓ δ u f asgn) ?_
  calc ∏ j : Fin (ℓ + 1), (rowList C ℓ δ u f asgn j).card
      ≤ ∏ _j : Fin (ℓ + 1), L := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hrow j)
    _ = L ^ (ℓ + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ProximityGap.Attack05

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.Attack05.curveListSize_le_prod_rowList
#print axioms ProximityGap.Attack05.curveListSize_le_pow_of_rowList_le
