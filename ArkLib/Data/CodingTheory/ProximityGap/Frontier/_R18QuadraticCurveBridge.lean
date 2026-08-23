/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic

/-!
# Round 18: quadratic character sums as affine curve counts

This file isolates the elementary bridge needed to turn the remaining quartic Weil input into a
point-count input.  For a quadratic character `χ : F → ℝ` satisfying the fiber-count law

`#{y : F | y^2 = a} = 1 + χ a`,

the complete signed sum `∑_s χ (f s)` is exactly the affine double-cover point count

`#{(s,y) : F × F | y^2 = f s} - |F|`.

The statement is deliberately abstract about `χ`: later files can instantiate it with the
quadratic multiplicative character, while this file supplies the counting algebra with no analytic
input and no named residual.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Affine double-cover point count for `Y² = f(X)`, in fiber-sum normal form. -/
def affineDoubleCoverCount (f : F → F) : ℕ :=
  ∑ x : F, ((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card

/-- The fiber-count law for a real quadratic character:
`#{y | y² = a} = 1 + χ(a)`.  It is stated as a real identity to avoid integer-valued plumbing at
the bridge layer. -/
def QuadraticFiberLaw (χ : F → ℝ) : Prop :=
  ∀ a : F, (((Finset.univ : Finset F).filter fun y => y ^ 2 = a).card : ℝ) = 1 + χ a

/-- The fiber-sum normal form of the affine double-cover count. -/
theorem affineDoubleCoverCount_eq_sum_fibers (f : F → F) :
    (affineDoubleCoverCount f : ℝ)
      = ∑ x : F, (((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card : ℝ) := by
  classical
  unfold affineDoubleCoverCount
  norm_cast

/-- Exact bridge: the quadratic-character complete sum is the affine curve count minus `q`. -/
theorem sum_quadraticChar_eq_affineDoubleCoverCount_sub_card
    {χ : F → ℝ} (hχ : QuadraticFiberLaw χ) (f : F → F) :
    ∑ x : F, χ (f x) = (affineDoubleCoverCount f : ℝ) - (Fintype.card F : ℝ) := by
  classical
  have hcount := affineDoubleCoverCount_eq_sum_fibers f
  have hpoint : ∀ x : F,
      χ (f x) = (((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card : ℝ) - 1 := by
    intro x
    have := hχ (f x)
    linarith
  have hsumone : (∑ _x : F, (1 : ℝ)) = (Fintype.card F : ℝ) := by
    simp
  calc ∑ x : F, χ (f x)
      = ∑ x : F,
          ((((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card : ℝ) - 1) := by
          exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = (∑ x : F, (((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card : ℝ))
          - ∑ _x : F, (1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ x : F, (((Finset.univ : Finset F).filter fun y => y ^ 2 = f x).card : ℝ))
          - (Fintype.card F : ℝ) := by rw [hsumone]
    _ = (affineDoubleCoverCount f : ℝ) - (Fintype.card F : ℝ) := by rw [hcount]

/-- Hasse-style count control implies the corresponding complete quadratic-character sum bound. -/
theorem norm_sum_quadraticChar_le_of_affineDoubleCoverCount
    {χ : F → ℝ} (hχ : QuadraticFiberLaw χ) (f : F → F) {C : ℝ}
    (hC : ‖(affineDoubleCoverCount f : ℝ) - (Fintype.card F : ℝ)‖ ≤ C) :
    ‖∑ x : F, χ (f x)‖ ≤ C := by
  rwa [sum_quadraticChar_eq_affineDoubleCoverCount_sub_card hχ f]

/-- The same bridge in the customary genus-one normalization: if the affine count differs from
`q` by at most `3√q`, then the signed quadratic sum is bounded by `3√q`. -/
theorem norm_sum_quadraticChar_le_three_sqrt
    {χ : F → ℝ} (hχ : QuadraticFiberLaw χ) (f : F → F)
    (hHasse :
      ‖(affineDoubleCoverCount f : ℝ) - (Fintype.card F : ℝ)‖
        ≤ 3 * Real.sqrt (Fintype.card F : ℝ)) :
    ‖∑ x : F, χ (f x)‖ ≤ 3 * Real.sqrt (Fintype.card F : ℝ) :=
  norm_sum_quadraticChar_le_of_affineDoubleCoverCount hχ f hHasse

/-! ## The quartic face used by the fourth-moment lane -/

/-- The quartic polynomial attached to one quadruple of roots:
`(s-x₁)(s-x₂)(s-y₁)(s-y₂)`. -/
def quarticRootProduct (z : (F × F) × (F × F)) (s : F) : F :=
  (s - z.1.1) * (s - z.1.2) * ((s - z.2.1) * (s - z.2.2))

/-- A point-count form of the genus-one/Hasse input for one quartic quadruple. -/
def QuarticDoubleCoverCountInput (z : (F × F) × (F × F)) : Prop :=
  ‖(affineDoubleCoverCount (quarticRootProduct z) : ℝ) - (Fintype.card F : ℝ)‖
    ≤ 3 * Real.sqrt (Fintype.card F : ℝ)

/-- The exact point-count bridge specialized to the quartic root product. -/
theorem sum_quadraticChar_quarticRootProduct_eq_count_sub_card
    {χ : F → ℝ} (hχ : QuadraticFiberLaw χ) (z : (F × F) × (F × F)) :
    ∑ s : F, χ (quarticRootProduct z s)
      = (affineDoubleCoverCount (quarticRootProduct z) : ℝ) - (Fintype.card F : ℝ) :=
  sum_quadraticChar_eq_affineDoubleCoverCount_sub_card hχ (quarticRootProduct z)

/-- A Hasse-style point-count input for the quartic double cover gives the desired complete
quadratic-character sum bound for that quadruple. -/
theorem norm_sum_quadraticChar_quarticRootProduct_le_three_sqrt
    {χ : F → ℝ} (hχ : QuadraticFiberLaw χ) (z : (F × F) × (F × F))
    (hHasse : QuarticDoubleCoverCountInput z) :
    ‖∑ s : F, χ (quarticRootProduct z s)‖ ≤ 3 * Real.sqrt (Fintype.card F : ℝ) :=
  norm_sum_quadraticChar_le_three_sqrt hχ (quarticRootProduct z) hHasse

end ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.affineDoubleCoverCount_eq_sum_fibers
#print axioms
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.sum_quadraticChar_eq_affineDoubleCoverCount_sub_card
#print axioms
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.norm_sum_quadraticChar_le_three_sqrt
#print axioms
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.sum_quadraticChar_quarticRootProduct_eq_count_sub_card
#print axioms
  ArkLib.ProximityGap.Frontier.R18QuadraticCurveBridge.norm_sum_quadraticChar_quarticRootProduct_le_three_sqrt
