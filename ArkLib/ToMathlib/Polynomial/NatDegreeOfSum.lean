/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree of a finite sum of polynomials

* `Polynomial.natDegree_sum_lt_of_forall_lt`: if every summand `f i` (for `i ∈ s`) has
  `natDegree < n` with `n ≠ 0`, then the finite sum `∑ i ∈ s, f i` also has `natDegree < n`.
-/

namespace Polynomial

/--
The natural degree of a sum of polynomials is strictly less than $n$ (where $n > 0$)
if the natural degree of each individual summand is strictly less than $n$.
-/
theorem natDegree_sum_lt_of_forall_lt.{u_1, w}
    {ι : Type w} (s : Finset ι) {S : Type u_1} [Semiring S]
  {n : ℕ} [inst : NeZero n] (f : ι → Polynomial S) (h : ∀ i ∈ s, (f i).natDegree < n) :
  (∑ i ∈ s, f i).natDegree < n := by
  rw [←Nat.le_pred_iff_lt (by aesop (add safe forward [inst.out]) (add safe (by omega)))]
  exact natDegree_sum_le_of_forall_le _ _ <| fun i hi ↦
    Nat.le_pred_of_lt (h _ hi)

end Polynomial
