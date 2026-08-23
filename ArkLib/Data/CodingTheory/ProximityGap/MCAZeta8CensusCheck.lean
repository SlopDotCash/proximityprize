/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeta8Census

/-!
# The complete `n = 8` circuit census (#357 round 12(c)): the classification check

The kernel-verified classification: over all canonical admissible pair-triangles of
`μ₈`, the integer collinearity determinant (`detVec`) vanishes **iff** the triangle is
horizontal (equal exponent-sums), vertical (three antipodal pairs), or slanted (one
antipodal pair + two same-difference-class pairs satisfying the exponent relation
`2k ≡ i + j + d`). Pre-validated externally (canonical triangles: 40 det-zeros, 40
classified, zero mismatches); verified here by kernel evaluation (`census8_check`).

With `collinear_iff_detVec_eq_zero` (the coordinate bridge) and
`dependent_iff_collinear` (the pencil criterion), this constitutes the **complete wide-
circuit census of `μ₈` in characteristic zero**: exactly the three families — in
particular, **slanted completeness at the first smooth scale** is now machine-checked.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
`native_decide` — the check is pure kernel reduction.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeta8Census

/-! ## The classification predicates (canonical tuples: `p < p'`, `q < q'`, `r < r'`,
`p < q < r`) -/

/-- Horizontal: equal exponent sums mod 8. -/
def isHorizB (p p' q q' r r' : ℕ) : Bool :=
  ((p + p') % 8 == (q + q') % 8) && ((p + p') % 8 == (r + r') % 8)

/-- Vertical: three antipodal pairs. -/
def isVertB (p p' q q' r r' : ℕ) : Bool :=
  (p' == p + 4) && (q' == q + 4) && (r' == r + 4)

/-- The slanted exponent relation for an antipodal pair at `kp` and two
difference-class pairs `(i, i+di)`, `(j, j+dj)`. -/
def slrelB (kp i di j dj : ℕ) : Bool :=
  if di == dj then
    (2 * kp) % 8 == (i + j + di) % 8
  else if di + dj == 8 then
    (2 * kp) % 8 == (i + (j + dj) % 8 + di) % 8
  else
    false

/-- Slanted: one antipodal pair, two same-difference-class pairs, exponent relation. -/
def isSlantedB (p p' q q' r r' : ℕ) : Bool :=
  ((p' == p + 4) && slrelB p q (q' - q) r (r' - r)) ||
  ((q' == q + 4) && slrelB q p (p' - p) r (r' - r)) ||
  ((r' == r + 4) && slrelB r p (p' - p) q (q' - q))

/-- The classified form. -/
def classifiedB (p p' q q' r r' : ℕ) : Bool :=
  isHorizB p p' q q' r r' || isVertB p p' q q' r r' || isSlantedB p p' q q' r r'

/-- Canonical admissible tuple filter. -/
def canonicalB (p p' q q' r r' : ℕ) : Bool :=
  (p < p') && (q < q') && (r < r') && (p < q) && (q < r) &&
  (p' != q) && (p' != q') && (p' != r) && (p' != r') &&
  (q' != r) && (q' != r') && (p' < 8) && (q' < 8) && (r' < 8)

/-- The census check: over every canonical admissible triangle, `detVec = 0` iff the
triangle is of classified form. -/
def censusOK : Bool :=
  (List.range 8).all fun p =>
    (List.range 8).all fun p' =>
      (List.range 8).all fun q =>
        (List.range 8).all fun q' =>
          (List.range 8).all fun r =>
            (List.range 8).all fun r' =>
              !(canonicalB p p' q q' r r') ||
                (decide (detVec p p' q q' r r' = Z8.zero)
                  == classifiedB p p' q q' r r')

set_option maxHeartbeats 12000000 in
/-- **THE `n = 8` CENSUS CHECK** (kernel evaluation): the integer determinant vanishes
exactly on the three classified families, over every canonical admissible triangle. -/
theorem census8_check : censusOK = true := by decide

/-! ## Source audit -/

#print axioms census8_check

end ProximityGap.MCAZeta8Census
