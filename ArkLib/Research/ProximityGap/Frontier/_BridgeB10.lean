/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Bridge B10 — even-τ-exactness / odd-graded vanishing (target E6, #444)

The empirical 2-adic recursion E6 has two halves:
`#bad_{2n}(k, 2m') = #bad_n(k/2, m')` (even depth folds) and `#bad_{2n}(k, odd) = 0`
(odd graded pieces vanish). This file proves the **odd-vanishing** half from its
geometric core: a sum over the full subgroup `μ_{2n}` of a *nonzero* power is `0`.

Concretely, if `ω` is a `2n`-th root of unity (`ω^{2n} = 1`) and the chosen power `j`
is *not* a multiple of `2n` — equivalently `ω^j ≠ 1` — then the geometric sum
`∑_{i=0}^{2n-1} (ω^i)^j = 0`. Summing `x^j` over `x = ω^0,…,ω^{2n-1}` (the full subgroup)
of a nonzero power vanishes. The antipode `−1 = ω^n ∈ μ_{2n}` is the special case that
kills odd graded pieces: pairing `x ↦ −x` sends `x^{odd} ↦ −x^{odd}`.

This is `geom_sum_eq` specialized to a primitive-enough root; it is the char-free
combinatorial heart of E6's odd-vanishing, built on the same tower-split subgroup
geometry as `DyadicTowerRecursion`.

Issue #444 (bridge B10, target E6).
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB10

variable {F : Type*} [Field F]

/-- **Geometric core of E6 odd-vanishing.** If `r ≠ 1` and `r^N = 1` then the geometric
sum of `r` over the full subgroup `∑_{i<N} r^i = 0`. (Here `r = ω^j` is the value of a
nonzero power `j` on the generator `ω` of `μ_N`, `N = 2n`.) -/
theorem subgroup_geom_sum_eq_zero {r : F} {N : ℕ} (hr1 : r ≠ 1) (hrN : r ^ N = 1) :
    ∑ i ∈ Finset.range N, r ^ i = 0 := by
  rw [geom_sum_eq hr1, hrN, sub_self, zero_div]

end ArkLib.ProximityGap.BridgeB10

#print axioms ArkLib.ProximityGap.BridgeB10.subgroup_geom_sum_eq_zero
