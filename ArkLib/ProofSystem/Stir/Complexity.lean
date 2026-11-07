import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# STIR round count: degenerate zero-round case only

**Status.** The STIR round-complexity statement (the number of folding rounds `M` is
`O(log degree / log k)` for folding factor `k`) is **not** formalized in this file. The only
theorem here, `M_bound_of_eq_zero`, takes `M = 0` as an explicit hypothesis, so it is the
arithmetic zero-round special case `0 ≤ 1 · (log degree / log k)`. It gives no bound for a
positive number of rounds and does not relate `M` to the STIR parameter recurrence; that theorem
remains to be proved.
-/

open scoped Real

namespace ArkLib.ProofSystem.Stir

/-- Zero-round special case of the STIR round-count bound: under the explicit hypothesis
`M = 0`, `M ≤ c * (log degree / log k)` holds with `c = 1`, because `log degree / log k ≥ 0`
for `degree, k ≥ 2`.

This is **not** the general STIR bound `M = O(log degree / log k)` for a positive number of
rounds; that statement is not formalized. (Formerly named `M_bound`.) -/
theorem M_bound_of_eq_zero (degree k M : ℕ) (h : M = 0) (hd : degree ≥ 2) (hk : k ≥ 2) :
    ∃ c > (0 : ℝ), (M : ℝ) ≤ c * (Real.log (degree : ℝ) / Real.log (k : ℝ)) := by
  refine ⟨1, one_pos, ?_⟩
  subst h
  simp only [Nat.cast_zero, one_mul]
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hd)
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hk)

@[deprecated M_bound_of_eq_zero (since := "2026-10-28")]
alias M_bound := M_bound_of_eq_zero

end ArkLib.ProofSystem.Stir
