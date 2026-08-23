/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowMatrix

/-!
# Reconstruction-pencil branch (i): active-column Cramer degree

The Padé/reconstruction-pencil programme reduces the below-UDR closure to a
γ-linear reconstruction system.  In the generic branch, one maximal minor is nonzero.
Only the reconstruction-denominator columns carry γ, so Cramer's root count is governed
by the number of γ-active columns, not by the full square-minor size.

This file records the reusable linear-algebra brick: a square determinant whose column
`j` has γ-degree at most `1` for `j` in an active column set, and degree `0` otherwise,
has determinant degree at most the active-column count.  Consequently, any bad-scalar
set contained in the roots of one nonzero such minor has that same cardinality bound.
-/

open Finset Polynomial Matrix

namespace ProximityGap.WBPencil

variable {F : Type} [Field F]

/-- A determinant with γ-degree carried by only `active` columns has degree at most
`active.card`. -/
theorem natDegree_det_le_card_activeCols {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (active : Finset ι)
    (hA : ∀ i j, (A i j).natDegree ≤ if j ∈ active then 1 else 0) :
    A.det.natDegree ≤ active.card := by
  classical
  have hdet := natDegree_det_le_sum_colBound A
    (fun j => if j ∈ active then 1 else 0) hA
  have hsum : (∑ j : ι, if j ∈ active then 1 else 0) = active.card := by
    rw [Finset.sum_boole]
    simp
  simpa [hsum] using hdet

/-- Root-count form of `natDegree_det_le_card_activeCols`: if a bad-scalar set is
contained in the roots of one nonzero active-column minor, then it has at most
`active.card` elements. -/
theorem badScalars_card_le_activeCols_of_subset_minor_roots
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (active : Finset ι)
    (hA : ∀ i j, (A i j).natDegree ≤ if j ∈ active then 1 else 0)
    (bad : Finset F) (hminor : A.det ≠ 0) (hsub : bad.val ⊆ A.det.roots) :
    bad.card ≤ active.card := by
  have hbadle : bad.card ≤ (Multiset.card A.det.roots : ℕ) :=
    Multiset.card_le_card (Finset.val_le_iff_val_subset.2 hsub)
  have hcard : (Multiset.card A.det.roots : WithBot ℕ) ≤ A.det.degree :=
    Polynomial.card_roots hminor
  have hroots : (Multiset.card A.det.roots : ℕ) ≤ A.det.natDegree := by
    have hle : (Multiset.card A.det.roots : WithBot ℕ) ≤
        (A.det.natDegree : WithBot ℕ) :=
      le_trans hcard Polynomial.degree_le_natDegree
    exact_mod_cast hle
  exact le_trans hbadle (le_trans hroots (natDegree_det_le_card_activeCols A active hA))

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.natDegree_det_le_card_activeCols
#print axioms ProximityGap.WBPencil.badScalars_card_le_activeCols_of_subset_minor_roots
