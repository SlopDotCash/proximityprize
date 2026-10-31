/-
Copyright (c) 2026 TrapLord. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: TrapLord
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettRIMKernelTrivial

/-!
# The bare-`GZPCondition` Lovett premises are false for every `k ≥ 1` (#389 / r3_thm211)

`SymbolicMinorFromLovett ι F k` and `RIMKernelTrivialFromLovett ι F k` both take a generic zero
pattern `(e, δ)` with only `GZPCondition e δ k`. For `δ ≡ 0` that condition holds vacuously
(`gzpCondition_zero`: every `κ ≤ 0` has `∑ κ = 0`), and it puts no constraint on `e`. With every
edge empty and `t = 1`, the reduced intersection matrix has **no rows** but `k ≥ 1` columns:

* `not_symbolicMinorFromLovett` — no row selection `Fin 1 × Fin k → RIMRowIdx e` exists at all,
  so `SymbolicMinorFromLovett ι F k` is false;
* `not_rimKernelTrivialFromLovett` — the constant-`1` vector lies in the kernel, so
  `RIMKernelTrivialFromLovett ι F k` is false.

Both hold for every edge type `ι`, every field `F` and every `k ≥ 1`. Lovett's Theorem 1.7, the
premise of both residuals, is supplied by the in-tree `lovettThm17_unconditional`.
`rimKernelTrivialFromLovett_refuted` already refutes the second residual at the single instance
`(Fin 1, ℚ, 1)`; this file covers every instance.

Consequence: the routes to `AGL24.SymbolicFullRankResidual` that take one of these premises are
vacuous for every `k ≥ 1` (and `SymbolicFullRankResidual F 0` is trivial, since
`Fin t × Fin 0` is empty):

* `symbolicFullRank_lovett_free`, `lovettSystemToDualSpan_of_connector`,
  `gmmDsResidual_unconditional` (premise `SymbolicMinorFromLovett`);
* `symbolicMinorFromLovett_of_ringChange`, `gmmDsDualZeroPatternTheoremPinned_via_lovett`,
  `symbolicFullRank_via_lovett_pinned` (premise `RIMKernelTrivialFromLovett`).
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

omit [DecidableEq ι] in
/-- `GZPCondition e 0 k` holds for every edge family: a multiplicity vector `κ ≤ 0` is zero,
so the hypothesis `0 < ∑ κ` never holds. -/
theorem gzpCondition_zero {V : Type*} [Fintype V] [DecidableEq V] (e : ι → Finset V) (k : ℕ) :
    AGL24.GZPCondition e (fun _ => 0) k := by
  intro κ hκ hpos
  exfalso
  have hz : ∀ j, κ j = 0 := fun j => Nat.le_zero.mp (hκ j)
  simp [hz] at hpos

/-- The empty edge family on two vertices: its reduced intersection matrix has no rows. -/
abbrev emptyEdges (ι : Type*) : ι → Finset (Fin (1 + 1)) := fun _ => ∅

omit [Fintype ι] [DecidableEq ι] in
theorem isEmpty_rimRowIdx_emptyEdges : IsEmpty (AGL24.RIMRowIdx (emptyEdges ι)) :=
  ⟨fun r => absurd r.2.property.1 (Finset.notMem_empty _)⟩

/-- **`SymbolicMinorFromLovett` is false for every `k ≥ 1`.** At `t = 1`, `e ≡ ∅`, `δ ≡ 0`
the premise `GZPCondition` holds, but the matrix has no rows, so no row selection
`Fin 1 × Fin k → RIMRowIdx e` exists. -/
theorem not_symbolicMinorFromLovett {k : ℕ} (hk : 1 ≤ k) : ¬ SymbolicMinorFromLovett ι F k := by
  intro h
  obtain ⟨rows, -, -⟩ := h (fun _ => lovettThm17_unconditional) (emptyEdges ι) (fun _ => 0)
    (gzpCondition_zero _ k)
  exact isEmpty_rimRowIdx_emptyEdges.elim (rows (0, ⟨0, hk⟩))

/-- **`RIMKernelTrivialFromLovett` is false for every `k ≥ 1`.** At `t = 1`, `e ≡ ∅`, `δ ≡ 0`
the matrix has no rows, so the constant-`1` vector is a nonzero kernel vector. -/
theorem not_rimKernelTrivialFromLovett {k : ℕ} (hk : 1 ≤ k) :
    ¬ RIMKernelTrivialFromLovett ι F k := by
  intro h
  have hmul : (AGL24.RIM F (emptyEdges ι)).mulVec
      (fun _ : Fin 1 × Fin k => (1 : MvPolynomial ι F)) = 0 := by
    funext r
    exact isEmpty_rimRowIdx_emptyEdges.elim r
  have hv := congrFun (h (fun _ => lovettThm17_unconditional) (emptyEdges ι) (fun _ => 0)
    (gzpCondition_zero _ k) _ hmul) (0, ⟨0, hk⟩)
  exact one_ne_zero hv

#print axioms not_symbolicMinorFromLovett
#print axioms not_rimKernelTrivialFromLovett

end ArkLib.GMMDS
