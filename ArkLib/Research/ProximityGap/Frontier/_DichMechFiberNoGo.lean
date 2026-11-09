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

So **there is no ambient top-coefficient matching**: `P = A² − u·O²` is a genuine degree-`a`
polynomial in `F[X]`.  This refutes exactly the proposed step "the high-degree part forces `u^a`
terms to match", i.e. leading-coefficient cancellation in the ambient polynomial ring.

**Scope (audit R-134, 2026-10-28).**  Ambient degree alone does **not** show that the subgroup
roots of `P` are not cut by a lower-degree equation.  On `μ_m` one may reduce modulo `X^m − 1`
(or take `gcd(P, X^m − 1)`): the subgroup-restricted residual is `P mod (X^m − 1)` and the isolated
roots are the roots of `gcd(P, X^m − 1)`, whose degree can be far below `deg P`.  The checked
fixture below (`restricted_residual_counterexample`) takes `m = 4` in `F₁₇`, `A = X^4`, `O = 1`:
`P = X^8 − X` has degree `8` with uncancelled leading term, yet on every `x ∈ μ_4` it equals
`1 − x`, a linear polynomial, and `O` never vanishes.  So the degree lemmas below exclude the
ambient-cancellation step only; they do not exclude every lower-degree fiber/genus description or
polynomial bound on the subgroup root set.

Numerics (probes `/tmp/probe_dich_{why,final}.py`, 1593+ engineered configs, q ≈ 2⁹…2¹², n ∈
{16,32}) were reported to show the count tracking the **design knobs** `dE + dO + 3` (= γ, the
`dE+1` coeffs of `E`, the `dO+1` coeffs of `O`), NOT `deg O`: at `deg O = 0` fixed, `|iso|` grows
`4,5,6,7` as `deg E` grows `0,1,2,3`, with measured ceiling `|iso| ≤ (dE+dO+3)+1 = k+2 = t`.  This
is **historical probe evidence, not formalized here**: those root counts may disprove a particular
universal `deg O`-type root-count bound, but no root count is proved in this file.  It is
consistent with the `_IsolatedCountKelley` finding that the residual is the open Kelley
general-position subgroup-root count.

So the specific DICH ambient-matching argument **does not** close `isolated ≤ poly(k)`
char-free; whether some other lower-degree/genus approach (e.g. via the restricted residual)
does so is **not decided** by this file.

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
formal refutation of the proposed *ambient leading-coefficient cancellation* step: when `A²`
strictly dominates `X·O²` in degree — which holds in the prize direction,
`deg A² = a > 1 + 2·deg O ≥ deg(X·O²)` — the difference `P = A² − X·O²` keeps the full degree of
`A²` in `F[X]`.  It does **not** show that the subgroup roots of `P` avoid a lower-degree equation:
the restricted residual `P mod (X^m − 1)` can have much lower degree (see
`restricted_residual_counterexample`). -/
theorem natDegree_isoP_eq_of_dominant (A O : F[X])
    (hdom : (X * O ^ 2).natDegree < (A ^ 2).natDegree) :
    (isoP A O).natDegree = (A ^ 2).natDegree := by
  unfold isoP
  exact natDegree_sub_eq_left_of_natDegree_lt hdom

/-- **The dominance hypothesis is satisfied in the prize direction** (char-free).  If
`1 + 2·deg O < (A²).natDegree` (e.g. `deg A² = a ≈ n` while `deg O < k/2`), then `X·O²` is
strictly dominated, so `natDegree_isoP_eq_of_dominant` applies and `deg P = deg A²`.  In words:
the perfect-square head re-introduces the degree-`a` term that the assignment hoped would match
away in the ambient ring; it never does (this says nothing about the restricted residual). -/
theorem prize_direction_no_matching (A O : F[X])
    (hprize : 1 + 2 * O.natDegree < (A ^ 2).natDegree) :
    (isoP A O).natDegree = (A ^ 2).natDegree :=
  natDegree_isoP_eq_of_dominant A O (lt_of_le_of_lt (natDegree_X_mul_O_sq_le O) hprize)

/-! ## Scope fixture: high ambient degree, linear restricted residual (audit R-134) -/

/-- `17` is prime, so `ZMod 17` is a field (local instance for the fixture). -/
local instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `μ_4 ⊂ ZMod 17` as an explicit list. -/
def mu4 : List (ZMod 17) := [1, 4, 13, 16]

/-- Every listed point is a 4th root of unity. -/
theorem mu4_pow4 : ∀ x ∈ mu4, x ^ 4 = 1 := by decide

/-- Evaluation of `P = isoP (X^4) 1` at a point. -/
theorem eval_isoP_X4_one (x : ZMod 17) :
    (isoP (X ^ 4 : (ZMod 17)[X]) 1).eval x = (x ^ 4) ^ 2 - x * 1 ^ 2 := by
  simp [isoP]

/-- **Counterexample to the over-broad reading of the degree lemma.**  For `A = X^4`, `O = 1` over
`F₁₇`, the dominance hypothesis holds and `P = X^8 − X` has full degree `8`, yet on every point of
`μ_4` it agrees with the linear polynomial `1 − x` (and `O = 1` never vanishes).  So the subgroup
root set of a degree-dominant `P` can be cut by an equation of degree far below `deg P`. -/
theorem restricted_residual_counterexample :
    (isoP (X ^ 4 : (ZMod 17)[X]) 1).natDegree = 8 ∧
      ∀ x ∈ mu4, (isoP (X ^ 4 : (ZMod 17)[X]) 1).eval x = 1 - x := by
  refine ⟨?_, ?_⟩
  · rw [prize_direction_no_matching _ _ (by simp [← pow_mul])]
    simp [← pow_mul]
  · intro x hx
    rw [eval_isoP_X4_one]
    revert x
    decide

/-- Documentation anchor: the DICH-mechanism's proposed *ambient* top-coefficient matching does not
occur (`deg P = a`).  This does not by itself reduce the isolated count to the Kelley/BGK quantity
`_IsolatedCountKelley.KelleyGeneralPositionConjecture`, nor exclude lower-degree descriptions via
the restricted residual `P mod (X^m − 1)` (see `restricted_residual_counterexample`); the specific
ambient-matching mechanism does NOT close `isolated ≤ poly(k)` char-free. -/
def dichFiberNoGoNote : Unit := ()

end ProximityGap.Frontier.DichMechFiberNoGo

#print axioms ProximityGap.Frontier.DichMechFiberNoGo.natDegree_X_mul_O_sq_le
#print axioms ProximityGap.Frontier.DichMechFiberNoGo.natDegree_isoP_eq_of_dominant
#print axioms ProximityGap.Frontier.DichMechFiberNoGo.prize_direction_no_matching
#print axioms ProximityGap.Frontier.DichMechFiberNoGo.restricted_residual_counterexample
