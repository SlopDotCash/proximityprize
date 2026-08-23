/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# `q`-ary entropy function

ABF26 Definition 2.2: the `q`-ary entropy function `H_q : (0, 1) → ℝ`.

  `H_q(x) := x · log_q(q-1) - x · log_q(x) - (1-x) · log_q(1-x)`

For `q = 2` this is the standard binary entropy. Used in:

- ABF26 Corollary 3.8 (volume-based lower bound for `|Λ(C, δ)|`).
- ABF26 Theorem 3.11 (random-linear-code lower bound).
- ABF26 Theorem 4.17 (capacity-regime CA breakdown).
-/

namespace CodingTheory

open Real

/-- **ABF26 Definition 2.2.** `q`-ary entropy function:

  `H_q(x) := x · log_q(q-1) - x · log_q(x) - (1-x) · log_q(1-x)`.

For `q = 2` this reduces to the standard binary entropy function. Mathlib's convention
`Real.log 0 = 0` makes the boundary cases `qEntropy q 0 = 0` and
`qEntropy q 1 = log_q (q-1)` well-defined (treating `0 · log 0 = 0` and
`log_q 1 = 0` automatically).

**Boundary behaviour for `q ≤ 1`.** The paper assumes `q ≥ 2` (alphabet size of an
error-correcting code). For `q ∈ {0, 1}`, `Real.logb q _` is identically `0` (since
`Real.log q = 0` there), so `qEntropy 0 x = qEntropy 1 x = 0` regardless of `x`. This
is mathematically uninformative but well-defined; downstream consumers that need a
meaningful q-ary entropy should guard with `2 ≤ q` themselves (as T4.17 does with
`10 ≤ Fintype.card F`, and T3.11 does via `Nat.Prime q`).

The paper's `H_S(x) := H_{|S|}(x)` set-entropy overload is provided as a wrapper at the
call site (a one-line `qEntropy (Fintype.card S) x`). -/
noncomputable def qEntropy (q : ℕ) (x : ℝ) : ℝ :=
  x * Real.logb q (q - 1) - x * Real.logb q x - (1 - x) * Real.logb q (1 - x)

@[simp]
lemma qEntropy_zero (q : ℕ) : qEntropy q 0 = 0 := by
  simp [qEntropy]

end CodingTheory
