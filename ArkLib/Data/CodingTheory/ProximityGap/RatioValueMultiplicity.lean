/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Ratio value-multiplicity: a rational function repeats a value ≤ deg times (#389, face (iv))

The face-(iv) line–ball incidence engine (`HighMultiplicityBadCount.lean`) reduces the per-error-
line bad-scalar count to the *multiplicity profile* of the ratio sequence `i ↦ −e₀ i / e₁ i`, and
its `highMult_empty_of_lt` lever vanishes the bad set once the demanded agreement exceeds the
**maximum value-multiplicity** of that ratio.  This file supplies the elementary algebraic bound
on that multiplicity in its **cross-multiplied** form: for polynomials `P, Q` with
`P − c·Q ≠ 0`, the level set `{x : P(x) = c·Q(x)}` has at most `max(deg P, deg Q)` points.

**Scope of the rational-function reading (audit PG-060).**  The theorems count the
cross-multiplied level set `P(x) = c·Q(x)`, not the value set of a rational function.  The two
agree only away from the zeros of `Q`: at a point with `Q(x) = 0` the rational function `P/Q` has
a pole (or a common zero of `P` and `Q`), so it has no value there in the usual partial
interpretation, and Lean's total division gives `P(x)/Q(x) = P(x)/0 = 0`.  Example: `P = X`,
`Q = X²`, `c = 1`: `P − c·Q = X − X² ≠ 0` and the cross-multiplied set contains `x = 0`, yet
`P(0)/Q(0) = 0/0 = 0 ≠ 1`.  Statements or applications phrased in terms of the values of `P/Q`
must therefore add the restriction `Q(x) ≠ 0` (on that subset the level sets coincide, and the
bound below still applies to it).  Likewise, applying the bound to the ratio `−e₀ i / e₁ i` of an
error line requires an explicit hypothesis that the error rows `e₀, e₁` are evaluations of
bounded-degree polynomials `P, Q` on the domain; error words `u − c` of a received word are not
low-degree in general, so this is an extra representative hypothesis, not automatic for
Reed–Solomon / generalized-RS lines.

This is the structure side of the H-EXT inverse direction (see `docs/research/proximity-gap/DISPROOF_LOG.md` O159): a value
attained with anomalously high multiplicity forces the level set `{x : P(x) = c·Q(x)}` to be large,
which a nonzero polynomial of bounded degree cannot allow — so high-multiplicity ratios are
*algebraically structured* (the numerator/denominator must collude, `P − c·Q ≡ 0`).

* `value_mult_le_natDegree` — for `P, Q : F[X]` with `P − c·Q ≠ 0` and any finite `S ⊆ F`,
  `#{x ∈ S : P(x) = c·Q(x)} ≤ (P − c·Q).natDegree`: the level set is a subset of the roots of the
  nonzero polynomial `P − c·Q`.
* `value_mult_le_max` — the clean degree bound `≤ max(deg P, deg Q)`.
* `highValue_forces_collusion` — the inverse form: if some value is attained more than
  `max(deg P, deg Q)` times, then `P − c·Q ≡ 0`, i.e. `P = c·Q` identically (the ratio is the
  constant `c`).  This is the local structure theorem the supply census consumes: anomalous
  multiplicity ⟹ algebraic degeneracy.

Unconditional, axiom-clean.  See `docs/kb/deltastar-literature-findings-2026-06-13.md` (faces
(iii)/(iv), the ratio-census route; Cilleruelo–Garaev concentration-of-points sharpens the bound
when `S` is a multiplicative subgroup orbit).
-/

open Polynomial

namespace ArkLib.ProximityGap.RatioMultiplicity

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Ratio value-multiplicity ≤ degree of `P − c·Q`.**  The points of a finite set `S` on the
cross-multiplied level set `P(x) = c·Q(x)` — the roots of `P − c·Q` in `S` — number at most
`(P − c·Q).natDegree`, provided `P − c·Q ≠ 0`.  Away from the zeros of `Q` these are exactly
the points where the rational function `P/Q` takes the value `c`; at zeros of `Q` the two notions
differ (see the module docstring), so a rational-value reading needs `Q(x) ≠ 0`. -/
theorem value_mult_le_natDegree (P Q : F[X]) (c : F) (h : P - C c * Q ≠ 0) (S : Finset F) :
    (S.filter (fun x => P.eval x = c * Q.eval x)).card ≤ (P - C c * Q).natDegree := by
  have hsub : (S.filter (fun x => P.eval x = c * Q.eval x)).val ⊆ (P - C c * Q).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    rw [Polynomial.mem_roots']
    refine ⟨h, ?_⟩
    change (P - C c * Q).eval x = 0
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hx.2, sub_self]
  exact Polynomial.card_le_degree_of_subset_roots hsub

/-- **Ratio value-multiplicity ≤ max(deg P, deg Q).**  The clean, symmetric degree bound: for
`deg P, deg Q ≤ d` and `P − c·Q ≠ 0`, the cross-multiplied level set `P(x) = c·Q(x)` has at most
`d` points of a finite set.  (Read as a statement about values of the rational function `P/Q`, it
applies on the points with `Q(x) ≠ 0`, where the two level sets coincide.) -/
theorem value_mult_le_max (P Q : F[X]) (c : F) (h : P - C c * Q ≠ 0) (S : Finset F) :
    (S.filter (fun x => P.eval x = c * Q.eval x)).card ≤ max P.natDegree Q.natDegree := by
  refine (value_mult_le_natDegree P Q c h S).trans ?_
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  gcongr
  exact Polynomial.natDegree_C_mul_le c Q

/-- **The inverse/structure form (H-EXT local step).**  If the cross-multiplied level set
`P(x) = c·Q(x)` has more than `max(deg P, deg Q)` points of `S`, then `P − c·Q` must be the zero
polynomial — i.e. `P = c·Q` identically.  Anomalously high multiplicity of this level set forces
algebraic degeneracy (numerator and denominator collude).  For the rational-value reading of
`P/Q`, restrict `S` to points with `Q(x) ≠ 0` first.
This is the local certificate the smooth-domain supply census needs — every
high-multiplicity ratio comes from a structured (degenerate) family. -/
theorem highValue_forces_collusion (P Q : F[X]) (c : F) (S : Finset F)
    (hlarge : max P.natDegree Q.natDegree
        < (S.filter (fun x => P.eval x = c * Q.eval x)).card) :
    P - C c * Q = 0 := by
  by_contra h
  exact absurd (value_mult_le_max P Q c h S) (not_le.mpr hlarge)

end ArkLib.ProximityGap.RatioMultiplicity

#print axioms ArkLib.ProximityGap.RatioMultiplicity.value_mult_le_natDegree
#print axioms ArkLib.ProximityGap.RatioMultiplicity.value_mult_le_max
#print axioms ArkLib.ProximityGap.RatioMultiplicity.highValue_forces_collusion
