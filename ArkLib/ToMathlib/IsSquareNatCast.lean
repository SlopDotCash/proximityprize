/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Cast.Basic

/-!
# `IsSquare` reflection through an injective `Nat.cast`

Mathlib provides `IsSquare.map` (pushing a square forward along a monoid hom) but no lemma pulling
`IsSquare` *back* through an injective `Nat.cast` given a cast-witnessed square root. This is the
reusable arithmetic step behind the BCIKS20 perfect-square Johnson-boundary characterization
(`BoundaryCardResidual.lean`, issue #64): once the real identity `(sqrtRate · |ι|)^2 = deg · |ι|`
is in hand over `ℝ≥0`, this lemma concludes `IsSquare (deg · |ι|)` in `ℕ`.
-/

/-- `IsSquare` reflects through an injective `Nat.cast`: for a `CharZero` semiring `R`, if
`(a : R) = (m : R) ^ 2` then `a` is a square in `ℕ`. -/
theorem isSquare_of_natCast_eq_sq_natCast {R : Type*} [Semiring R] [CharZero R]
    {a m : ℕ} (h : (a : R) = (m : R) ^ 2) : IsSquare a := by
  rw [isSquare_iff_exists_sq]
  refine ⟨m, Nat.cast_injective (R := R) ?_⟩
  rw [Nat.cast_pow]
  exact h

#print axioms isSquare_of_natCast_eq_sq_natCast
