/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCurve

/-!
# Per-level Bézout degree bound for the GV tower decomposition (#389)

Each tower level `L_j(c) = #{w∈μ_{2^k} : (w+1)^{2^j} = −c^{2^j}}` (from `GVObjectTowerDecomposition`)
is the root-count, inside `μ_{2^k}`, of the degree-`2^j` polynomial `(X+1)^{2^j} + c^{2^j}`:

> **`tower_level_card_le`** — `L_j(c) ≤ 2^j`.

This is the explicit per-level Bézout bound (the char-0 value is `≤ 2` per level by circle geometry;
the char-`p` surplus is what makes the *top* level `j=k−1` carry the GV hardness). It completes the
tower decomposition `r(c) ≤ 1 + ∑_{j<k} L_j(c)` quantitatively. Axiom-clean. Issue #389.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.GVTowerLevel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-level Bézout bound.** The `j`-th tower level has at most `2^j` solutions in `μ_{2^k}`. -/
theorem tower_level_card_le {k j : ℕ} (c : F) :
    ((muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))).card ≤ 2 ^ j := by
  classical
  set P : F[X] := (X + C 1) ^ (2 ^ j) + C (c ^ (2 ^ j)) with hP
  have hdeg_base : (X + C (1 : F)).natDegree = 1 := natDegree_X_add_C 1
  have hdeg_pow : ((X + C (1 : F)) ^ (2 ^ j)).natDegree = 2 ^ j := by
    rw [natDegree_pow, hdeg_base, mul_one]
  have hPdeg : P.natDegree = 2 ^ j := by
    rw [hP, natDegree_add_C, hdeg_pow]
  have hPne : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPdeg
    exact (pow_pos (by norm_num : (0 : ℕ) < 2) j).ne hPdeg
  -- the filter set is contained in the roots of `P`
  have hsub : (muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))
      ⊆ P.roots.toFinset := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, IsRoot.def, hP]
    simp only [eval_add, eval_pow, eval_X, eval_C]
    linear_combination hw.2
  calc ((muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'
    _ = 2 ^ j := hPdeg

end ArkLib.ProximityGap.GVTowerLevel

#print axioms ArkLib.ProximityGap.GVTowerLevel.tower_level_card_le
