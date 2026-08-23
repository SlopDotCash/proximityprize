/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Minimal `m*` crossing-depth substrate (#444)

This restores the missing dependency consumed by `_V7GeometricDecayLogCrossing`.  The original V7
file only needs the elementary crossing-depth API: given an envelope `D : ℕ → ℕ`, a budget `n`, and
a witness that some depth crosses the budget, define the first crossing depth and prove the standard
minimality lemma.

Scope: pure `Nat.find` bookkeeping.  No incidence estimate, no CORE/BGK/capacity claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.MStarLognReduction

/-- `mStar D n h` is the first depth `m` at which the envelope `D` reaches budget `n`. -/
noncomputable def mStar (D : ℕ → ℕ) (n : ℕ) (h : ∃ m, D m ≤ n) : ℕ :=
  Nat.find h

/-- The first crossing depth really crosses the budget. -/
theorem mStar_spec (D : ℕ → ℕ) (n : ℕ) (h : ∃ m, D m ≤ n) :
    D (mStar D n h) ≤ n := by
  exact Nat.find_spec h

/-- Minimality of `mStar`: any explicit crossing depth bounds the first crossing depth. -/
theorem mStar_le_of_le (D : ℕ → ℕ) (n : ℕ) (h : ∃ m, D m ≤ n) {m : ℕ}
    (hm : D m ≤ n) :
    mStar D n h ≤ m := by
  exact Nat.find_min' h hm

/-- Named predicate used by the surrounding dossier: the budget is reached by depth `m`. -/
def logBudgetReached (D : ℕ → ℕ) (n m : ℕ) : Prop :=
  D m ≤ n

/-- If the named crossing predicate holds at `m`, then `mStar ≤ m`. -/
theorem mStar_le_of_upperEnvelope_crossing (D : ℕ → ℕ) (n : ℕ) (h : ∃ m, D m ≤ n)
    {m : ℕ} (hm : logBudgetReached D n m) :
    mStar D n h ≤ m :=
  mStar_le_of_le D n h hm

end ArkLib.ProximityGap.MStarLognReduction

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.MStarLognReduction.mStar_spec
#print axioms ArkLib.ProximityGap.MStarLognReduction.mStar_le_of_le
#print axioms ArkLib.ProximityGap.MStarLognReduction.mStar_le_of_upperEnvelope_crossing
