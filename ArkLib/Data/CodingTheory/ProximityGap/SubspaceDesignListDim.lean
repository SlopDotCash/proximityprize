/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignJointAgree


/-!
# The list-dimension bound from a subspace design (B2 list-decoding) (#389, #334)

The linear-algebraic core of list decoding from subspace designs, assembling
`subspaceDesign_jointAgree_card_le` (joint agreement is small) with inclusion–exclusion.

`subspaceDesign_list_dim_bound`: if `r+1` codewords of a `τ`-subspace design each agree with a word
`y` on `≥ a` coordinates and `a` is large enough (`τ(r)·n + r·n < (r+1)·a`), then their differences
`c_{j+1} − c₀` are linearly **dependent**.  By inclusion–exclusion the *common* agreement set has
`≥ (r+1)a − r·n` coordinates; independent differences would cap it at `τ(r)·n`
(`subspaceDesign_jointAgree_card_le`), contradicting the threshold.

Consequence: the close codewords span a subspace of dimension `< r`, so iterating (down to the first
`r` with `τ(r)·n + r·n ≥ (r+1)·a`) pins the entire list inside a low-dimensional affine subspace —
the structural step the curve-decodability producer needs before the `exists_separating`-based
pruning finishes the count.  Axiom-clean.
-/
open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {F : Type} [Field F] [DecidableEq F]

/-- **The list-dimension bound from a subspace design.**  If `r+1` codewords of a `τ`-subspace
design each agree with a word `y` on `≥ a` coordinates, and `a` is large enough that
`τ(r)·n + r·n < (r+1)·a`, then their differences `c_{j+1} − c₀` are linearly **dependent**.
By inclusion–exclusion the common agreement set has `≥ (r+1)a − r·n` coordinates; if the differences
were independent the joint-agreement bound would cap it at `τ(r)·n`, contradicting the threshold.
Hence the list of close codewords spans a subspace of dimension `< r` — the linear-algebraic core of
list decoding from subspace designs (iterating pins the list inside a low-dimensional subspace). -/
theorem subspaceDesign_list_dim_bound {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) (c : Fin (r + 1) → (ι → Fin s → F)) (hc : ∀ j, c j ∈ C)
    (y : ι → Fin s → F) {a : ℕ}
    (hagree : ∀ j, a ≤ (univ.filter (fun i => c j i = y i)).card)
    (hbig : τ r * Fintype.card ι + r * Fintype.card ι < (r + 1) * a) :
    ¬ LinearIndependent F (fun j : Fin r => c j.succ - c 0) := by
  classical
  intro hindep
  set S := univ.filter (fun i => ∀ j, c j i = y i) with hSdef
  have han : a ≤ Fintype.card ι :=
    le_trans (hagree 0) (le_trans (Finset.card_le_card (Finset.subset_univ _))
      (le_of_eq Finset.card_univ))
  -- inclusion–exclusion: `(r+1)·a ≤ |S| + r·n`
  have hScard : (r + 1) * a ≤ S.card + r * Fintype.card ι := by
    have hpart : S.card + (univ.filter (fun i => ¬ ∀ j, c j i = y i)).card = Fintype.card ι := by
      rw [hSdef, ← Finset.card_univ (α := ι)]
      exact Finset.card_filter_add_card_filter_not (s := univ) (fun i => ∀ j, c j i = y i)
    have hcompsub : univ.filter (fun i => ¬ ∀ j, c j i = y i)
        ⊆ univ.biUnion (fun j : Fin (r + 1) => univ.filter (fun i => c j i ≠ y i)) := by
      intro i hi
      rw [mem_filter] at hi
      obtain ⟨j, hj⟩ := not_forall.mp hi.2
      exact Finset.mem_biUnion.mpr ⟨j, mem_univ j, mem_filter.mpr ⟨mem_univ i, hj⟩⟩
    have hcompcard : (univ.filter (fun i => ¬ ∀ j, c j i = y i)).card
        ≤ (r + 1) * (Fintype.card ι - a) := by
      calc (univ.filter (fun i => ¬ ∀ j, c j i = y i)).card
          ≤ (univ.biUnion (fun j : Fin (r + 1) =>
              univ.filter (fun i => c j i ≠ y i))).card := Finset.card_le_card hcompsub
        _ ≤ ∑ _j : Fin (r + 1), (Fintype.card ι - a) := by
            refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun j _ => ?_))
            have hpartj : (univ.filter (fun i => c j i = y i)).card
                + (univ.filter (fun i => c j i ≠ y i)).card = Fintype.card ι := by
              rw [← Finset.card_univ (α := ι)]
              exact Finset.card_filter_add_card_filter_not (s := univ) (fun i => c j i = y i)
            calc (univ.filter (fun i => c j i ≠ y i)).card
                = Fintype.card ι - (univ.filter (fun i => c j i = y i)).card := by omega
              _ ≤ Fintype.card ι - a := Nat.sub_le_sub_left (hagree j) _
        _ = (r + 1) * (Fintype.card ι - a) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hd1 : (r + 1) * a + (r + 1) * (Fintype.card ι - a) = (r + 1) * Fintype.card ι := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' han]
    have hd2 : (r + 1) * Fintype.card ι = Fintype.card ι + r * Fintype.card ι := by ring
    omega
  -- the joint-agreement bound caps `|S|` at `τ(r)·n`
  have hSle : (S.card : ℝ) ≤ τ r * Fintype.card ι :=
    subspaceDesign_jointAgree_card_le h hr c hc hindep y S (fun i hi => (mem_filter.mp hi).2)
  -- contradiction
  have hcast : ((r + 1) * a : ℝ) ≤ τ r * Fintype.card ι + r * Fintype.card ι := by
    calc ((r + 1) * a : ℝ) ≤ (S.card : ℝ) + r * Fintype.card ι := by exact_mod_cast hScard
      _ ≤ τ r * Fintype.card ι + r * Fintype.card ι := by linarith
  linarith

end ProximityGap
