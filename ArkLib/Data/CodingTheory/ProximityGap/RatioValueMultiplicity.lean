/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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
on that multiplicity: when the ratio is a genuine *rational function* `P/Q` of bounded degree —
the case for Reed–Solomon / generalized-RS error lines, whose coordinates are low-degree
polynomials evaluated on the domain — every value is attained at most `max(deg P, deg Q)` times.

This is the structure side of the H-EXT inverse direction (see `DISPROOF_LOG.md` O159): a value
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

/-- **Ratio value-multiplicity ≤ degree of `P − c·Q`.**  The coordinates where the rational
function `P/Q` takes the value `c` — equivalently the roots of `P − c·Q` — number at most
`(P − c·Q).natDegree`, over any finite set `S`, provided `P − c·Q ≠ 0`. -/
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

/-- **Ratio value-multiplicity ≤ max(deg P, deg Q).**  The clean, symmetric degree bound: a
rational function `P/Q` with `deg P, deg Q ≤ d` attains any value `c` at most `d` times on a finite
set (unless it is identically `c`). -/
theorem value_mult_le_max (P Q : F[X]) (c : F) (h : P - C c * Q ≠ 0) (S : Finset F) :
    (S.filter (fun x => P.eval x = c * Q.eval x)).card ≤ max P.natDegree Q.natDegree := by
  refine (value_mult_le_natDegree P Q c h S).trans ?_
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  gcongr
  exact Polynomial.natDegree_C_mul_le c Q

/-- **The inverse/structure form (H-EXT local step).**  If the value `c` is attained by `P/Q` on
more than `max(deg P, deg Q)` points of `S`, then `P − c·Q` must be the zero polynomial — i.e.
`P = c·Q` identically.  Anomalously high ratio-multiplicity forces algebraic degeneracy: the only
way a bounded-degree rational function over-attains a value is for the numerator and denominator to
collude.  This is the local certificate the smooth-domain supply census needs — every
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
