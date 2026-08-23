/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The polynomial fold decomposition (#389, the supply fold-recursion engine)

The δ* supply wall (issue #389) is **self-similar** under the FRI/tower fold `x ↦ x²`:
the fold halves both the agreement floor and the Johnson radius, so it preserves
sub-Johnson-ness — which is why the supply recursion bottoms out only after `log n`
levels (the KKH26 `1/log n` arithmetic). This file lands the algebraic engine of that
recursion: the even/odd fold of a polynomial and the **antipodal fiber-agreement
equivalence**.

* `foldEven p := contract 2 p`, `foldOdd p := contract 2 p.divX` — the even/odd folds.
* `fold_decomposition` — **`p = (foldEven p).comp(X²) + X · (foldOdd p).comp(X²)`** for
  every polynomial over a commutative ring: the canonical even/odd split.
* `foldEven_natDegree_le` / `foldOdd_natDegree_le` — the degree halving: a degree-`< k`
  polynomial folds to a pair of polynomials of degree `≤ deg p / 2` — the parameter
  halving the recursion needs.
* `eval_pos` / `eval_neg` — `p(x) = foldEven p (x²) + x · foldOdd p (x²)` and
  `p(−x) = foldEven p (x²) − x · foldOdd p (x²)`.
* `fiber_agreement_iff` — **over a field of characteristic ≠ 2**: `p` agrees with values
  `wp` at `x` and `wm` at `−x` **iff** `foldEven p (x²) = (wp+wm)/2` and
  `x · foldOdd p (x²) = (wp−wm)/2`. The fold bijection is what injects the
  full-fiber-agreement part of the level-`n` supply into the level-`n/2` supply.

This is the provable engine of the supply recursion; the residual singleton (half-fiber)
stratum is the localized open core of the multiplicative-side wall (issue #389 thread).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #389 (the bold-pinning-hypothesis comment: the supply fold recursion);
  `KKH26FoldStability.lean` (the KKH26 family's fold fixed-point, R2 refutation).
-/

open Polynomial

namespace ArkLib.ProximityGap.PolynomialFold

variable {R : Type*} [CommRing R]

/-- The even fold: `(foldEven p).coeff i = p.coeff (2i)`. -/
noncomputable def foldEven (p : R[X]) : R[X] := contract 2 p

/-- The odd fold: `(foldOdd p).coeff i = p.coeff (2i+1)`. -/
noncomputable def foldOdd (p : R[X]) : R[X] := contract 2 p.divX

theorem coeff_foldEven (p : R[X]) (i : ℕ) : (foldEven p).coeff i = p.coeff (2 * i) := by
  rw [foldEven, coeff_contract (by norm_num) p i, mul_comm]

theorem coeff_foldOdd (p : R[X]) (i : ℕ) : (foldOdd p).coeff i = p.coeff (2 * i + 1) := by
  rw [foldOdd, coeff_contract (by norm_num) p.divX i, coeff_divX, mul_comm]

/-- `(X · expand 2 h)` has zero coefficient at even degrees. -/
private theorem coeff_X_expand_even (h : R[X]) (j : ℕ) :
    (X * expand R 2 h).coeff (2 * j) = 0 := by
  rcases j with _ | j'
  · rw [Nat.mul_zero, mul_coeff_zero, coeff_X_zero, zero_mul]
  · have he : 2 * (j' + 1) = (2 * j' + 1) + 1 := by ring
    rw [he, coeff_X_mul, coeff_expand (by norm_num : 0 < 2)]
    rw [if_neg (by omega)]

/-- **The fold decomposition**: every polynomial is its even fold (in `X²`) plus `X` times
its odd fold (in `X²`). -/
theorem fold_decomposition (p : R[X]) :
    p = (foldEven p).comp (X ^ 2) + X * (foldOdd p).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow]
  ext n
  rw [coeff_add]
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- n = j + j even
    have hn : n = 2 * j := by omega
    subst hn
    rw [coeff_expand_mul' (by norm_num : 0 < 2), coeff_foldEven,
      coeff_X_expand_even, add_zero]
  · -- n = 2j + 1 odd
    subst hj
    have he : (expand R 2 (foldEven p)).coeff (2 * j + 1) = 0 := by
      rw [coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
    rw [he, zero_add, coeff_X_mul, coeff_expand_mul' (by norm_num : 0 < 2),
      coeff_foldOdd]

theorem foldEven_natDegree_le (p : R[X]) :
    (foldEven p).natDegree ≤ p.natDegree / 2 := by
  rw [foldEven, contract]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro i _
  by_cases h : p.coeff (i * 2) = 0
  · simp [h]
  · refine le_trans (natDegree_monomial_le _) ?_
    have : i * 2 ≤ p.natDegree := le_natDegree_of_ne_zero h
    omega

theorem foldOdd_natDegree_le (p : R[X]) :
    (foldOdd p).natDegree ≤ p.natDegree / 2 := by
  rw [foldOdd, contract]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro i _
  by_cases h : p.divX.coeff (i * 2) = 0
  · simp [h]
  · refine le_trans (natDegree_monomial_le _) ?_
    rw [coeff_divX] at h
    have : i * 2 + 1 ≤ p.natDegree := le_natDegree_of_ne_zero h
    omega

theorem eval_foldEven_sq (p : R[X]) (x : R) :
    ((foldEven p).comp (X ^ 2)).eval x = (foldEven p).eval (x ^ 2) := by
  rw [eval_comp, eval_pow, eval_X]

theorem eval_foldOdd_sq (p : R[X]) (x : R) :
    ((foldOdd p).comp (X ^ 2)).eval x = (foldOdd p).eval (x ^ 2) := by
  rw [eval_comp, eval_pow, eval_X]

/-- `p(x) = foldEven p (x²) + x · foldOdd p (x²)`. -/
theorem eval_pos (p : R[X]) (x : R) :
    p.eval x = (foldEven p).eval (x ^ 2) + x * (foldOdd p).eval (x ^ 2) := by
  conv_lhs => rw [fold_decomposition p]
  rw [eval_add, eval_mul, eval_X, eval_foldEven_sq, eval_foldOdd_sq]

/-- `p(−x) = foldEven p (x²) − x · foldOdd p (x²)`. -/
theorem eval_neg (p : R[X]) (x : R) :
    p.eval (-x) = (foldEven p).eval (x ^ 2) - x * (foldOdd p).eval (x ^ 2) := by
  conv_lhs => rw [fold_decomposition p]
  rw [eval_add, eval_mul, eval_X, eval_foldEven_sq, eval_foldOdd_sq]
  simp only [neg_sq]
  ring

/-- **The antipodal fiber-agreement equivalence** (field, char ≠ 2): `p` matches the
prescribed values `wp` at `x` and `wm` at `−x` iff its even fold matches the half-sum at
`x²` and its odd fold (scaled by `x`) matches the half-difference. This is the local
core of the supply fold recursion: a full-fiber agreement of `p` is exactly a joint
agreement of `(foldEven p, foldOdd p)` at the folded point `x²`. -/
theorem fiber_agreement_iff {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    (p : F[X]) (x wp wm : F) :
    (p.eval x = wp ∧ p.eval (-x) = wm)
      ↔ ((foldEven p).eval (x ^ 2) = (wp + wm) / 2
          ∧ x * (foldOdd p).eval (x ^ 2) = (wp - wm) / 2) := by
  rw [eval_pos p x, eval_neg p x]
  set E := (foldEven p).eval (x ^ 2) with hE
  set O := x * (foldOdd p).eval (x ^ 2) with hO
  rw [eq_div_iff hchar, eq_div_iff hchar]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · linear_combination h1 + h2
    · linear_combination h1 - h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · refine mul_right_cancel₀ hchar ?_
      linear_combination h1 + h2
    · refine mul_right_cancel₀ hchar ?_
      linear_combination h1 - h2

/-! ## Source audit -/

#print axioms fold_decomposition
#print axioms foldEven_natDegree_le
#print axioms foldOdd_natDegree_le
#print axioms fiber_agreement_iff

end ArkLib.ProximityGap.PolynomialFold
