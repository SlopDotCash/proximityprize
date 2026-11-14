/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# The DICH-mechanism Wronskian/transversality route does NOT cut the isolated locus (#407)

HONEST NEGATIVE (a `*_NoGo`-style record, not a closure).  Companion to
`_DichMechFiberNoGo.lean`: that file refutes **route (1)** of the DICH-mechanism (the proposed
"top-coefficient matching" fiber collapse, which fails because `deg(A² − u·O²) = deg A² = a`, the
top term is never cancelled).  This file refutes **route (2)** — the Wronskian / derivative idea —
which `_DichMechFiberNoGo` did not address.

## The route (2) proposal

An isolated root `u ∈ μ_{n/2}` satisfies `A(u)² = u·O(u)²` with `O(u) ≠ 0`, i.e. for the rational
function `R = A/O` (whose number of **poles** is `deg O < k/2`, *even though* `deg A ≈ n`) we have
`R(u)² = u`.  Route (2) hopes: an isolated root is a **simple/transverse** intersection of
`{y² = u}` with `{y = R(u)}`, so a Wronskian / Mason–Stothers argument on the **low-pole** `R`
should bound the isolated count by `deg O`, not `deg A`.

The natural Wronskian object is `W = A'·O − A·O'` (the numerator of `R' = (A/O)'`, since
`R' = (A'O − AO')/O²`).  Two things would be needed for route (2) to give an `O(deg O)` cut:
(i) `W` vanishes at isolated roots (so they are roots of a *fixed* polynomial), and
(ii) `deg W = O(deg O)`.  **Both fail.**

## What is PROVEN here (char-free, exact)

* `isoF_derivative_eq` / `isolated_multiple_root_iff` — the exact derivative formula
  `F'(u) = 2 A(u) A'(u) − O(u)² − 2 u O(u) O'(u)` for `F = A² − X·O²`, and the iff: `u` is a
  root of `F'` (i.e. a *multiple* root of `F` when also `F(u) = 0`) exactly when the tangency
  relation `2 A(u) A'(u) = O(u)² + 2 u O(u) O'(u)` holds.

  **Audit correction (R-335).** An earlier version of this header "differentiated" the root
  equality `R(u)² = u` to `2 R(u) R'(u) = 1` and concluded `W(u) ≠ 0` at every isolated root, and
  that isolated roots are simple.  Both steps are invalid: an equality at ONE point is not a
  rational-function identity and cannot be differentiated.  Checked counterexamples over `ℚ`
  (with `u = 1 ∈ μ_{n/2}` and `A(u), O(u), u` all nonzero):
  - `simple_root_with_zero_wronskian`: `A = O = 1` gives `F = 1 − X`, a SIMPLE root at `1`, yet
    `W = A'O − AO' = 0` identically — so a simple isolated root can be a Wronskian root;
  - `isolated_root_can_be_multiple`: `A = (X+1)/2`, `O = 1` gives `F = (X−1)²/4`, a MULTIPLE
    isolated root at `1` — so isolation (in the displayed sense) does not imply simplicity.

  Transversality at a root therefore needs an explicit hypothesis (e.g. `F'(u) ≠ 0`, or a
  stated nonvanishing of `W(u)`), not a pointwise differentiation.  The numerical observation
  that `W` vanished at `15 / 43298 ≈ 0.03%` of sampled isolated roots is probe data only.

* `natDegree_wronskian_le` / `wronskian_eq_derivative_of_O_one` — the degree UPPER bound
  `deg W ≤ deg A + deg O`, and the exact identity `W = A'` when `O = 1`.  This shows that an
  arbitrary small `deg O` (even `O = 1`) can leave a Wronskian of degree up to `deg A − 1`, so
  small `deg O` alone does not force a small Wronskian.  It is an upper bound / example, not a
  lower bound on `deg W` in every characteristic or for every structured `(A, O)`.

## Conclusion (scope of the negative result)

What is proved: the derivative formula and its root iff, the Wronskian degree upper bound, and
the `O = 1` example showing that low `deg O` does not by itself make the Wronskian low-degree.
What is NOT proved: that no low-degree auxiliary polynomial vanishes on the isolated locus, nor
that every Wronskian / Mason–Stothers / structured-subgroup argument fails under the intended
ragged/subgroup conditions.  The naive version of route (2) (requirement (i) "isolated roots are
Wronskian roots", requirement (ii) "`deg W = O(deg O)`") is not supported by these facts, and the
isolated count remains tied to the open subgroup-root count of `F` (compare
`_IsolatedCountKelley.KelleyGeneralPositionConjecture`), but this file is not a proof of a
method-wide exclusion.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.DichMechWronskianNoGo

open Polynomial

variable {F : Type*} [Field F]

/-- The Wronskian numerator `W = A'·O − A·O'` of `R' = (A/O)'`. -/
noncomputable def wronskian (A O : F[X]) : F[X] :=
  derivative A * O - A * derivative O

/-- **Exact derivative formula for `F = A² − X·O²`.**

`F'(u) = 2 A(u) A'(u) − O(u)² − 2 u O(u) O'(u)` for every `u`.  This is the quantity whose
nonvanishing expresses transversality (simplicity) of a root `u` of `F`.  Note that a root
equality `A(u)² = u·O(u)²` at one point does NOT imply `F'(u) ≠ 0` or `W(u) ≠ 0`: see
`simple_root_with_zero_wronskian` and `isolated_root_can_be_multiple` below; transversality must
be assumed explicitly. -/
theorem isoF_derivative_eq (A O : F[X]) (u : F) :
    (A ^ 2 - X * O ^ 2).derivative.eval u
      = 2 * A.eval u * (derivative A).eval u
        - (O.eval u) ^ 2 - 2 * u * O.eval u * (derivative O).eval u := by
  simp only [derivative_sub, derivative_pow, derivative_mul, derivative_X,
    eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X, Nat.cast_ofNat, eval_C,
    Nat.reduceSub, pow_one]
  ring

/-- **Multiple-root (tangency) characterization.**

`u` is a root of `F'` for `F = A² − X·O²` iff `2 A(u) A'(u) = O(u)² + 2 u O(u) O'(u)`.  When also
`F(u) = 0` this is exactly the condition that `u` is a multiple root of `F`.  It holds for some
isolated roots (`isolated_root_can_be_multiple`), so isolated roots need not be simple; whether
it fails generically is not proved here. -/
theorem isolated_multiple_root_iff (A O : F[X]) (u : F) :
    (A ^ 2 - X * O ^ 2).derivative.IsRoot u ↔
      2 * A.eval u * (derivative A).eval u
        = (O.eval u) ^ 2 + 2 * u * O.eval u * (derivative O).eval u := by
  rw [IsRoot.def, isoF_derivative_eq]
  constructor <;> intro h <;> linear_combination h

/-- **Wronskian degree UPPER bound: `deg W ≤ deg A + deg O`.**

This is an upper bound only.  It is not an equality or lower bound in an arbitrary
characteristic (e.g. `W = 0` for `A = O = 1`), and by itself it does not exclude a lower-degree
auxiliary polynomial or a structured subgroup argument.  Together with
`wronskian_eq_derivative_of_O_one` it shows that small `deg O` alone does not force a small
Wronskian bound. -/
theorem natDegree_wronskian_le (A O : F[X]) :
    (wronskian A O).natDegree ≤ A.natDegree + O.natDegree := by
  unfold wronskian
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · calc (derivative A * O).natDegree
        ≤ (derivative A).natDegree + O.natDegree := natDegree_mul_le
      _ ≤ A.natDegree + O.natDegree :=
          Nat.add_le_add_right ((natDegree_derivative_le A).trans (Nat.sub_le _ _)) _
  · calc (A * derivative O).natDegree
        ≤ A.natDegree + (derivative O).natDegree := natDegree_mul_le
      _ ≤ A.natDegree + O.natDegree :=
          Nat.add_le_add_left ((natDegree_derivative_le O).trans (Nat.sub_le _ _)) _

/-- **`O = 1` gives `W = A'`.**

With `O = 1` (`deg O = 0`) the Wronskian is exactly `derivative A`, whose degree can be as large
as `deg A − 1` (e.g. in characteristic `0` for `deg A ≥ 1`).  So no bound of the form
`deg W ≤ c·deg O` independent of `A` holds in general.  This is an example for arbitrary `A`; it
does not by itself exclude arguments using additional structure of the actual `(A, O)`. -/
theorem wronskian_eq_derivative_of_O_one (A : F[X]) :
    wronskian A 1 = derivative A := by
  unfold wronskian
  simp [derivative_one]

/-- **Counterexample: a simple isolated root that IS a Wronskian root.**  Over `ℚ`, `A = O = 1`,
`u = 1`: the root equality `A(u)² = u·O(u)²` holds with all quantities nonzero, `F = 1 − X` has
`u = 1` as a SIMPLE root (`F'(1) ≠ 0`), and yet `W = A'O − AO' = 0`.  So a root equality cannot be
differentiated as an identity to conclude `W(u) ≠ 0`. -/
theorem simple_root_with_zero_wronskian :
    ((1 : ℚ[X]).eval 1) ^ 2 = (1 : ℚ) * ((1 : ℚ[X]).eval 1) ^ 2 ∧
    ((1 : ℚ[X]) ^ 2 - X * (1 : ℚ[X]) ^ 2).IsRoot 1 ∧
    ¬ ((1 : ℚ[X]) ^ 2 - X * (1 : ℚ[X]) ^ 2).derivative.IsRoot 1 ∧
    wronskian (1 : ℚ[X]) 1 = 0 := by
  refine ⟨by simp, by simp, ?_, by simp [wronskian]⟩
  rw [isolated_multiple_root_iff]
  simp

/-- **Counterexample: an isolated root that is a MULTIPLE root.**  Over `ℚ`, `A = (X+1)/2`,
`O = 1`, `u = 1`: `A(1) = 1`, so the root equality holds with all quantities nonzero, but
`F = A² − X = (X−1)²/4` has `u = 1` as a double root (`F(1) = F'(1) = 0`).  So isolation in the
displayed sense does not imply simplicity. -/
theorem isolated_root_can_be_multiple :
    ((C (1 / 2 : ℚ) * (X + 1)).eval 1) ^ 2 = (1 : ℚ) * ((1 : ℚ[X]).eval 1) ^ 2 ∧
    (C (1 / 2 : ℚ) * (X + 1)).eval 1 ≠ 0 ∧
    ((C (1 / 2 : ℚ) * (X + 1)) ^ 2 - X * (1 : ℚ[X]) ^ 2).IsRoot 1 ∧
    ((C (1 / 2 : ℚ) * (X + 1)) ^ 2 - X * (1 : ℚ[X]) ^ 2).derivative.IsRoot 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [isolated_multiple_root_iff]
  simp only [eval_mul, eval_C, eval_add, eval_X, eval_one, derivative_mul, derivative_C,
    derivative_add, derivative_X, derivative_one]
  norm_num

/-- Documentation anchor (scope of this file): the derivative formula, its root iff, the
Wronskian degree upper bound and the `O = 1` example are proved; the naive route (2)
requirements are not supported by them; and the two counterexamples above show that isolated
roots may be Wronskian roots and may be multiple.  This marker is NOT a proof that every
Wronskian / auxiliary-polynomial / structured-subgroup argument fails, nor that the isolated count
reduces only to `_IsolatedCountKelley.KelleyGeneralPositionConjecture`. -/
def dichWronskianNoGoNote : Unit := ()

end ProximityGap.Frontier.DichMechWronskianNoGo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.isoF_derivative_eq
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.isolated_multiple_root_iff
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.natDegree_wronskian_le
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.wronskian_eq_derivative_of_O_one
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.simple_root_with_zero_wronskian
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.isolated_root_can_be_multiple
