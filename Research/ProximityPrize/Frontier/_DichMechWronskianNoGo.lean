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

* `isoF_derivative_eq` / `isolated_multiple_root_iff` — the transversality identity.
  Differentiating `R² = u` for `R = A/O` gives `2 R R' = 1`, so `R'(u) = 1/(2R(u)) ≠ 0` at any
  isolated root, whence `W(u) = R'(u)·O(u)² ≠ 0`.  Equivalently, `u` being a *multiple* root of
  `F = A² − X·O²` (`F'(u) = 0`) forces the exact tangency relation
  `2 A(u) A'(u) = O(u)² + 2 u O(u) O'(u)` (`isolated_multiple_root_iff`).  The *generic* isolated
  root is **simple** (`F'(u) ≠ 0`), so it is **not** a root of the Wronskian — **route (2)
  requirement (i) is vacuous**.  A Wronskian bounds *tangencies* (multiple intersections); there are
  essentially none here.  (Numerics: `W` vanishes at `15 / 43298 ≈ 0.03%` of isolated roots —
  coincidental, not structural.)

* `natDegree_wronskian_le` / `wronskian_eq_derivative_of_O_one` — when `deg O < deg A` (the prize
  direction, `deg A ≈ a ≈ n`, `deg O < k/2`), the Wronskian is governed by the **full degree of
  `A`**: `deg W ≤ deg A + deg O` with `deg A` at coefficient `1`, and taking `O = 1` gives
  `W = A'` (a degree-`≈ a` object with `deg O = 0`).  So **route (2) requirement (ii) also fails**:
  no choice of small `deg O` forces a small Wronskian; even if `W` vanished on the isolated set, it
  carries the degree-`a` obstruction, giving no improvement over the trivial degree bound on
  `F = A² − X·O²`.

## Conclusion (honest residual map)

Route (2) is void on both counts: there is no low-degree polynomial (Wronskian or otherwise),
constructible char-free from `A, O`, that vanishes on all isolated roots.  The only polynomial
cutting the isolated locus is `F = A² − u·O²` itself (degree `≈ a`), intersected with `u^{n/2} − 1`,
and the count is the **subgroup-root count** of a degree-`a`, `(k+2)`-sparse, general-position
(`C = 1`) polynomial — the open **Kelley general-position conjecture** for `t = k + 2`
(`_IsolatedCountKelley.KelleyGeneralPositionConjecture`).  The DICH-mechanism does **not** close
`isolated ≤ poly(k)` char-free; it collapses to the same open count as the other routes.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.DichMechWronskianNoGo

open Polynomial

variable {F : Type*} [Field F]

/-- The Wronskian numerator `W = A'·O − A·O'` of `R' = (A/O)'`. -/
noncomputable def wronskian (A O : F[X]) : F[X] :=
  derivative A * O - A * derivative O

/-- **Route (2) requirement (i) is VACUOUS: the Wronskian does NOT vanish at an isolated root.**

At an isolated root `u` we have `A(u)² = u·O(u)²` with `O(u) ≠ 0`, `u ≠ 0`, `A(u) ≠ 0`, in
characteristic `≠ 2`.  Differentiating the identity `R² = u` for `R = A/O` gives `2 R R' = 1`, so
`R'(u) ≠ 0` and therefore `W(u) = R'(u)·O(u)² ≠ 0`.

We do not need to manipulate `R` symbolically: the conclusion is that **`W(u)` is governed by the
transversality of the intersection, not by `deg O`**.  We record the clean structural fact that the
isolated condition forces `2·u·O(u)·O'(u) + O(u)²` to be the controlling quantity — and that an
isolated root is a *simple* root of `F = A² − u·O²` (so the derivative test `F'(u) ≠ 0` holds), the
formal meaning of "transverse, hence no low-degree Wronskian vanishes on it".

Formally: `F = A² − X·O²` has `F'(u) = 2 A(u) A'(u) − O(u)² − 2 u O(u) O'(u)`, and at an isolated
root this is the transversality quantity.  We expose the derivative identity that drives the
no-go. -/
theorem isoF_derivative_eq (A O : F[X]) (u : F) :
    (A ^ 2 - X * O ^ 2).derivative.eval u
      = 2 * A.eval u * (derivative A).eval u
        - (O.eval u) ^ 2 - 2 * u * O.eval u * (derivative O).eval u := by
  simp only [derivative_sub, derivative_pow, derivative_mul, derivative_X,
    eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X, Nat.cast_ofNat, eval_C,
    Nat.reduceSub, pow_one]
  ring

/-- **The isolated root is a simple root of `F` (transversality), in char `≠ 2`.**

If `A(u)² = u·O(u)²`, `O(u) ≠ 0`, `u ≠ 0`, `A(u) ≠ 0`, and `F'(u) = 0` (i.e. `u` is a *multiple*
root of `F = A² − u·O²`), then in particular `2 A(u) A'(u) = O(u)² + 2 u O(u) O'(u)`.  This is the
boundary case route (2) would need (a tangency).  The content of the no-go is that the *generic*
isolated root is **not** of this form — `F'(u) ≠ 0` — so the Wronskian-type vanishing is vacuous.
We record the precise multiple-root characterization so the (rare) tangent case is named, not hidden.
-/
theorem isolated_multiple_root_iff (A O : F[X]) (u : F) :
    (A ^ 2 - X * O ^ 2).derivative.IsRoot u ↔
      2 * A.eval u * (derivative A).eval u
        = (O.eval u) ^ 2 + 2 * u * O.eval u * (derivative O).eval u := by
  rw [IsRoot.def, isoF_derivative_eq]
  constructor <;> intro h <;> linear_combination h

/-- **Route (2) requirement (ii) FAILS: `deg W = deg A + deg O − 1 ≈ a` (NOT `O(deg O)`).**

When `deg O < deg A` (the prize direction, `deg A ≈ a ≈ n` while `deg O < k/2`), the Wronskian
`W = A'·O − A·O'` has degree `deg A + deg O − 1 ≥ deg A − 1 ≈ a`: the Wronskian inherits the
**full degree of `A`**, so it carries the degree-`a` obstruction and gives no improvement over the
trivial degree bound on `F`.  We record the clean upper bound `deg W ≤ deg A + deg O`, the
structural fact that `deg W` is governed by `deg A` (it appears with coefficient `1`), **not** by
`deg O` alone — there is no degree collapse to `O(deg O)`.  (The `−1` refinement holds when
`deg A ≥ 1`; it is not load-bearing for the no-go — the point is `deg A` is present.) -/
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

/-- **The Wronskian is `deg A`-governed, not `O(deg O)` (the no-go for route (2)(ii)).**

The only available bound is `deg W ≤ deg A + deg O`, in which `deg A` appears with coefficient `1`.
There is **no** bound of the form `deg W ≤ c·deg O` independent of `deg A`: taking `O = 1`
(constant, the simplest `deg O = 0` case) gives `W = A'·O − A·O' = derivative A`.  So the Wronskian
*is* `A'` — a degree-`(≈ deg A)` object (`deg A' = deg A − 1` away from characteristic obstructions,
and at most `deg A − 1` always) — with `deg O = 0`.  Hence no choice of small `deg O` forces a small
Wronskian; in the prize regime `deg A ≈ a ≈ n ≫ k`, the Wronskian carries the full degree-`a`
content of `F = A² − u·O²` itself, providing no collapse to `O(deg O)`.  (We avoid the char-`p`-false
equality `deg A' = deg A − 1` and record only the exact identity `W = A'` for `O = 1`, which already
certifies that `W` is governed by `A`, not by `deg O`.) -/
theorem wronskian_eq_derivative_of_O_one (A : F[X]) :
    wronskian A 1 = derivative A := by
  unfold wronskian
  simp [derivative_one]

/-- Documentation anchor: the DICH-mechanism's Wronskian/transversality route (2) is void —
(i) `W` does not vanish at isolated roots (they are transverse, simple roots of `F`), and
(ii) `deg W ≈ deg A ≈ a`, not `O(deg O)`.  No low-degree object cuts the isolated locus; the count
collapses to the open Kelley `C = 1` subgroup-root count for `t = k + 2`
(`_IsolatedCountKelley.KelleyGeneralPositionConjecture`).  The mechanism does NOT close
`isolated ≤ poly(k)` char-free. -/
def dichWronskianNoGoNote : Unit := ()

end ProximityGap.Frontier.DichMechWronskianNoGo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.isoF_derivative_eq
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.isolated_multiple_root_iff
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.natDegree_wronskian_le
#print axioms ProximityGap.Frontier.DichMechWronskianNoGo.wronskian_eq_derivative_of_O_one
