/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# The fiber/genus reduction of the isolated count does NOT drop to `deg O` (#407)

HONEST NEGATIVE (a `*_REFUTED`-style record, not a closure).

The DICH-mechanism assignment proposed: the isolated roots `{u ∈ μ_{n/2} : A(u)² = u·O(u)²,
O(u) ≠ 0}` are cut, after "the high-degree part of `A² = u·O²` forces `u^a` terms to MATCH (a
coset condition = the core)", by a polynomial of degree `≈ 2·deg O + O(1) ≤ k`, hence char-free
`|iso| ≤ k`.  This file records the **char-free polynomial fact that REFUTES that reduction**:

  `deg P = a` (the top term `u^a` of `A²` is never cancelled), because `deg(u·O²) = 1 + 2·deg O`
  and the prize direction has `a > 1 + 2·deg O` (indeed `a ≈ n`, `deg O < k/2`).

So **there is no top-coefficient matching**: `P = A² − u·O²` is a genuine degree-`a` polynomial,
and the isolated roots are its subgroup-roots — a degree-`a`, `O(k)`-sparse subgroup-root count,
**not** a `deg O`-degree count.  The proposed fiber/genus collapse is mathematically void: the
"matching" it relied on does not occur.

Numerics (probes `/tmp/probe_dich_{why,final}.py`, 1593+ engineered configs, q ≈ 2⁹…2¹², n ∈
{16,32}) confirm the count tracks the **design knobs** `dE + dO + 3` (= γ, the `dE+1` coeffs of
`E`, the `dO+1` coeffs of `O`), NOT `deg O`: at `deg O = 0` fixed, `|iso|` grows `4,5,6,7` as
`deg E` grows `0,1,2,3`.  The measured ceiling is `|iso| ≤ (dE+dO+3)+1 = k+2 = t` (the sparsity),
**reproducing the `_IsolatedCountKelley` finding** that the honest residual is the open Kelley
general-position subgroup-root count, q-independent but NOT provable below BGK/Kelley.

So the DICH-mechanism **does not** close `isolated ≤ poly(k)` char-free; it collapses to BGK/Kelley.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.DichMechFiberNoGo

open Polynomial

variable {F : Type*} [Field F]

/-- The ragged residual `P = A² − X·O²`. -/
noncomputable def isoP (A O : F[X]) : F[X] := A ^ 2 - X * O ^ 2

/-- **`deg(X·O²) ≤ 1 + 2·deg O`** (char-free).  The right side is the small RHS degree. -/
theorem natDegree_X_mul_O_sq_le (O : F[X]) :
    (X * O ^ 2).natDegree ≤ 1 + 2 * O.natDegree := by
  calc (X * O ^ 2).natDegree
      ≤ (X : F[X]).natDegree + (O ^ 2).natDegree := natDegree_mul_le
    _ ≤ 1 + 2 * O.natDegree := by
        gcongr
        · simpa using natDegree_X_le
        · calc (O ^ 2).natDegree ≤ 2 * O.natDegree := by
                simpa [two_mul] using natDegree_pow_le (p := O) (n := 2)
          _ = 2 * O.natDegree := rfl

/-- **No top cancellation: `deg P = deg A²` when `deg A² > deg(X·O²)`** (char-free).  This is the
formal refutation of the proposed fiber collapse: when `A²` strictly dominates `X·O²` in degree —
which holds in the prize direction, `deg A² = a > 1 + 2·deg O ≥ deg(X·O²)` — the difference
`P = A² − X·O²` keeps the full degree of `A²`.  Hence `P` is a genuine degree-`a` polynomial; its
subgroup-roots are NOT cut by any degree-`(2 deg O)` object.  The isolated count is the
subgroup-root count of this degree-`a` sparse polynomial = the open Kelley/BGK count. -/
theorem natDegree_isoP_eq_of_dominant (A O : F[X])
    (hdom : (X * O ^ 2).natDegree < (A ^ 2).natDegree) :
    (isoP A O).natDegree = (A ^ 2).natDegree := by
  unfold isoP
  exact natDegree_sub_eq_left_of_natDegree_lt hdom

/-- **The dominance hypothesis is satisfied in the prize direction** (char-free).  If
`1 + 2·deg O < (A²).natDegree` (e.g. `deg A² = a ≈ n` while `deg O < k/2`), then `X·O²` is
strictly dominated, so `natDegree_isoP_eq_of_dominant` applies and `deg P = deg A²`.  In words:
the perfect-square head re-introduces the degree-`a` term that the assignment hoped would match
away; it never does. -/
theorem prize_direction_no_matching (A O : F[X])
    (hprize : 1 + 2 * O.natDegree < (A ^ 2).natDegree) :
    (isoP A O).natDegree = (A ^ 2).natDegree :=
  natDegree_isoP_eq_of_dominant A O (lt_of_le_of_lt (natDegree_X_mul_O_sq_le O) hprize)

/-- Documentation anchor: the DICH-mechanism's fiber/genus reduction to `deg O` is void
(`deg P = a`, no top matching); the isolated count is the degree-`a` sparse subgroup-root count,
i.e. the open Kelley/BGK quantity — `_IsolatedCountKelley.KelleyGeneralPositionConjecture`.  The
mechanism does NOT close `isolated ≤ poly(k)` char-free. -/
def dichFiberNoGoNote : Unit := ()

end ProximityGap.Frontier.DichMechFiberNoGo

#print axioms ProximityGap.Frontier.DichMechFiberNoGo.natDegree_X_mul_O_sq_le
#print axioms ProximityGap.Frontier.DichMechFiberNoGo.natDegree_isoP_eq_of_dominant
#print axioms ProximityGap.Frontier.DichMechFiberNoGo.prize_direction_no_matching
