/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude(Anthropic), Vuk Dolijanovic
-/

import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.Data.MvPolynomial.WeightedDegree
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Restricting a multivariate polynomial to a line

Given two points `a b : Fin k → R`, the line through them is `t ↦ a + t • (b - a)`. Restricting
an `MvPolynomial (Fin k) R` to that line yields a univariate `Polynomial R`, obtained by
substituting the linear-in-`t` expression `aᵢ + t * (bᵢ - aᵢ)` for each variable `Xᵢ`.

GKR uses this construction to fold the two evaluation claims left by a layer's sum-check
(one at `x`, one at `y`) into a single claim. The prover sends the restriction of the
layer polynomial to the line through `x` and `y`, and the verifier reduces to one random
point on that line.

## Main results

* `MvPolynomial.natDegree_aeval_le`: substituting polynomials of degree at most `1` for the
  variables produces a univariate polynomial of degree at most the original's `totalDegree`.
  This specializes the weighted-degree substitution bound to unit weights.
* `MvPolynomial.totalDegree_le_of_multilinear`: a multilinear polynomial in `k` variables has
  total degree at most `k` (each monomial uses each of the `k` variables at most once).
* `MvPolynomial.natDegree_restrictToLine_le`: combining the two, a multilinear polynomial in
  `k` variables restricts to a line as a univariate polynomial of degree at most `k`.
-/

namespace MvPolynomial

variable {R : Type*} {σ : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Substituting polynomials of degree at most `1` for the variables of `V` yields a
univariate polynomial of degree at most `V.totalDegree`. -/
theorem natDegree_aeval_le (f : σ → Polynomial R) (hf : ∀ i, (f i).natDegree ≤ 1)
    (V : MvPolynomial σ R) :
    (aeval f V).natDegree ≤ V.totalDegree := by
  simpa only [weightedTotalDegree_one] using
    natDegree_aeval_le_weightedTotalDegree_of_le (1 : σ → ℕ) f V hf

/-- A multilinear polynomial in `k` variables has total degree at most `k`: every monomial
uses each of the `k` variables at most once. -/
theorem totalDegree_le_of_multilinear {k : ℕ} (V : MvPolynomial (Fin k) R)
    (hV : ∀ i, degreeOf i V ≤ 1) : V.totalDegree ≤ k := by
  simpa using totalDegree_le_card_mul_of_mem_restrictDegree V 1
    ((mem_restrictDegree_iff_degreeOf_le V 1).2 hV)

end CommSemiring

section CommRing

variable [CommRing R]

/-- The line through `pointA` and `pointB`, parameterized so that `t = 0` gives `pointA`
and `t = 1` gives `pointB`. -/
def line {k : ℕ} (pointA pointB : Fin k → R) (t : R) : Fin k → R :=
  pointA + t • (pointB - pointA)

@[simp]
theorem line_agrees_on_zero {k : ℕ} (pointA pointB : Fin k → R) :
    line pointA pointB 0 = pointA := by
  unfold line
  simp

@[simp]
theorem line_agrees_on_one {k : ℕ} (pointA pointB : Fin k → R) :
    line pointA pointB 1 = pointB := by
  unfold line
  simp

/-- `V` restricted to the line through `pointA` and `pointB`, kept symbolic in the line
parameter: each variable `Xᵢ` is replaced by `pointAᵢ + t * (pointBᵢ - pointAᵢ)`, which is
linear in `t`. The result is a univariate polynomial. -/
noncomputable def restrictToLine {k : ℕ} (pointA pointB : Fin k → R)
    (V : MvPolynomial (Fin k) R) : Polynomial R :=
  aeval (fun i => Polynomial.C (pointA i) + Polynomial.X * Polynomial.C (pointB i - pointA i)) V

/-- The defining property of `restrictToLine`: evaluating the restriction at `t` is the same
as evaluating `V` at the point `line pointA pointB t`. Without this the restriction and the
line are unrelated definitions that merely look alike. -/
@[simp]
theorem eval_restrictToLine {k : ℕ} (pointA pointB : Fin k → R)
    (V : MvPolynomial (Fin k) R) (t : R) :
    (restrictToLine pointA pointB V).eval t = eval (line pointA pointB t) V := by
  rw [restrictToLine, show Polynomial.eval t = (Polynomial.evalRingHom t : Polynomial R →+* R)
    from rfl, map_aeval]
  refine eval₂Hom_congr ?_ ?_ rfl
  · ext a
    simp
  · funext i
    simp [line]

/-- A multilinear polynomial in `k` variables restricts to a line as a univariate polynomial
of degree at most `k`. -/
theorem natDegree_restrictToLine_le {k : ℕ} (pointA pointB : Fin k → R)
    (V : MvPolynomial (Fin k) R) (hV : ∀ i, degreeOf i V ≤ 1) :
    (restrictToLine pointA pointB V).natDegree ≤ k := by
  refine le_trans (natDegree_aeval_le _ ?_ V) (totalDegree_le_of_multilinear V hV)
  intro i
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp only [Polynomial.natDegree_C, sup_le_iff, Nat.zero_le, true_and]
  exact le_trans Polynomial.natDegree_mul_le (by simp [Polynomial.natDegree_X_le])

end CommRing

end MvPolynomial
