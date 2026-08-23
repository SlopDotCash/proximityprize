/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListDimensionLift

/-!
# The deep-band supply closure: the affine-line list is Johnson-bounded

Issue #389. Composing the dimension-lift (`lineList_le_succ_agreement`: the affine-line list
of the dimension-`k` code is at most the per-word agreement list of `u₀` for the
dimension-`(k+1)` code) with the in-tree Johnson bound (`rsCode_agreement_list_card_le`
applied to `rsCode dom (k+1)`, whose distinct codewords agree on `≤ k` points) gives an
**unconditional polynomial bound on the affine-line list in the deep band**:

> **`lineList_le_johnson`** — for `k < n` and `n·k < a²`:
> `Λ(u₀, xᵏ) ≤ n² / (a² − n·k)`.

With `a = k+m+1`, the gap `n·k < a²` holds throughout the deep band (large `m`), so the
supply along bad-scalar lines is **closed unconditionally there**: a polynomial line list,
no per-word sub-Johnson blowup. The wall survives only the shallow band `a² ≤ n·k`. This is
the rigorous endpoint of the line-list route — the deep band of the supply statement,
discharged via lifting the code dimension by one and applying Johnson to the lift.

## References

* Issue #389; `LineListDimensionLift.lean` (`lineList_le_succ_agreement`),
  `JohnsonSplitSupply.lean` (`rsCode_agreement_list_card_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The deep-band supply closure.** For `k < n` and `n·k < a²` (the deep band), the
affine-line list along `u₁ = xᵏ` is polynomially bounded: `Λ ≤ n²/(a² − n·k)`. -/
theorem lineList_le_johnson (dom : Fin n ↪ F) (k a : ℕ) (hkn : k < n)
    (hgap : n * k < a ^ 2) (u₀ : Fin n → F) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ ∃ γ : F, a ≤ (agreeSet c (fun i => u₀ i + γ • (dom i) ^ k)).card)).card
      ≤ n ^ 2 / (a ^ 2 - n * k) := by
  classical
  -- the Johnson bound for the dimension-(k+1) code (pairwise agreement ≤ k)
  have hjohnson := rsCode_agreement_list_card_le dom (k := k + 1) (a := a)
    (by omega) u₀ (by simpa using hgap)
  -- (k+1) − 1 = k in the denominator
  have hkk : (k + 1) - 1 = k := by omega
  rw [hkk] at hjohnson
  exact le_trans (lineList_le_succ_agreement dom k a hkn u₀) hjohnson

/-! ## Source audit -/

#print axioms lineList_le_johnson

end ProximityGap.Ownership
