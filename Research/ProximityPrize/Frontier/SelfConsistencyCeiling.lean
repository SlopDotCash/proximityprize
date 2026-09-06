/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The pointwise-autocorrelation self-consistency ceiling is linear (#444)

This file formalizes the constraint lemma from `DISPROOF_LOG.md`: if the pointwise autocorrelation
identity is closed by the term-by-term triangle inequality, the resulting quadratic self-consistency
bound is only the trivial linear ceiling.

The analytic skeleton is:

```
  M^2 ≤ n + (n - 1) M
```

where `M` is the worst period and `n = |μ_n|`.  The theorem below proves that this inequality
can never force `M = O(√n)`: it implies only `M ≤ n`, and the value `M = n` saturates the
inequality exactly.

Honest scope: pure arithmetic packaging of an already probed wall.  It is not a character-sum
upper bound, not thinness-essential, and not a CORE proof.  It records that any proof using the
autocorrelation identity must exploit cancellation in the nontrivial shift sum, not bound those
shifts term-by-term.
-/

namespace ProximityGap.Frontier.SelfConsistencyCeiling

/-- **Linear ceiling from the self-consistency quadratic.**

If a nonnegative worst-period envelope `M` satisfies the triangle-inequality closure
`M^2 ≤ n + (n - 1) M`, then `M ≤ n`.  Thus this closure is linear in `n`, not
square-root in `n`.
The proof is just the contrapositive: if `M > n`, then both `M^2 > nM` and
`nM > n + (n-1)M`, contradicting the quadratic inequality. -/
theorem selfConsistency_ceiling_linear {n M : ℝ} (hn : 1 ≤ n) (hM : 0 ≤ M)
    (hquad : M ^ 2 ≤ n + (n - 1) * M) : M ≤ n := by
  by_contra hnot
  have hgt : n < M := lt_of_not_ge hnot
  have hnpos : 0 < n := by linarith
  have hMpos : 0 < M := lt_trans hnpos hgt
  have hsq_gt : n * M < M ^ 2 := by
    nlinarith [hgt, hMpos]
  have hrhs_lt : n + (n - 1) * M < n * M := by
    nlinarith [hgt]
  nlinarith

/-- Natural-cardinality wrapper for `selfConsistency_ceiling_linear`. -/
theorem selfConsistency_ceiling_linear_nat {n : ℕ} {M : ℝ} (hn : 1 ≤ n) (hM : 0 ≤ M)
    (hquad : M ^ 2 ≤ (n : ℝ) + ((n : ℝ) - 1) * M) : M ≤ (n : ℝ) := by
  exact selfConsistency_ceiling_linear (n := (n : ℝ)) (M := M)
    (by exact_mod_cast hn) hM hquad

/-- **Sharpness at the trivial bound.**  The linear value `M = n` saturates the same quadratic
exactly: `n^2 = n + (n-1)n`.  Hence the self-consistency inequality alone cannot distinguish
square-root cancellation from the trivial envelope. -/
theorem selfConsistency_saturated_at_linear (n : ℝ) :
    n ^ 2 = n + (n - 1) * n := by
  ring

/-- Natural-cardinality sharpness wrapper. -/
theorem selfConsistency_saturated_at_linear_nat (n : ℕ) :
    (n : ℝ) ^ 2 = (n : ℝ) + ((n : ℝ) - 1) * (n : ℝ) := by
  exact selfConsistency_saturated_at_linear (n := (n : ℝ))

end ProximityGap.Frontier.SelfConsistencyCeiling

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.SelfConsistencyCeiling.selfConsistency_ceiling_linear
#print axioms ProximityGap.Frontier.SelfConsistencyCeiling.selfConsistency_ceiling_linear_nat
#print axioms ProximityGap.Frontier.SelfConsistencyCeiling.selfConsistency_saturated_at_linear
#print axioms ProximityGap.Frontier.SelfConsistencyCeiling.selfConsistency_saturated_at_linear_nat
