/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The 2-adic tower factorization and the level decomposition of the GV object (#389)

The difference of `2^k`-th powers factors along the 2-adic tower:

> **`pow_two_pow_sub_eq`** — `a^{2^k} − b^{2^k} = (a − b) · ∏_{j<k} (a^{2^j} + b^{2^j})`.

Over a field this gives `a^{2^k} = b^{2^k} ⟺ a = b ∨ ∃ j<k, a^{2^j} = −b^{2^j}`
(`pow_two_pow_eq_iff`). Applied with `a = 1+w`, `b = c` to the curve form of the García–Voloch
object `r(c) = #{w∈μ_n : (1+w)^n = c^n}` (`n = 2^k`), this decomposes `r(c)` into **tower levels**:
`w` contributes at level `j` iff `(1+w)/c` has order exactly `2^{j+1}` (i.e.
`(1+w)^{2^j} = −c^{2^j}`). Each level is a separate, lower-degree intersection problem — the
structural skeleton of any
level-by-level bound on the GV object for 2-power subgroups. Axiom-clean. Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.TwoPowerTower

variable {R : Type*}

/-- **The 2-adic tower factorization.** `a^{2^k} − b^{2^k} = (a−b)·∏_{j<k}(a^{2^j}+b^{2^j})`. -/
theorem pow_two_pow_sub_eq [CommRing R] (a b : R) (k : ℕ) :
    a ^ (2 ^ k) - b ^ (2 ^ k) = (a - b) * ∏ j ∈ Finset.range k, (a ^ (2 ^ j) + b ^ (2 ^ j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    have e : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    rw [e, pow_mul, pow_mul]
    ring

/-- Over a field (no zero divisors): `a^{2^k} = b^{2^k}` iff `a = b` or some tower factor vanishes,
`a^{2^j} = −b^{2^j}` for some `j < k`. -/
theorem pow_two_pow_eq_iff [Field R] (a b : R) (k : ℕ) :
    a ^ (2 ^ k) = b ^ (2 ^ k) ↔ a = b ∨ ∃ j ∈ Finset.range k, a ^ (2 ^ j) = -b ^ (2 ^ j) := by
  have hfac := pow_two_pow_sub_eq a b k
  rw [← sub_eq_zero (a := a ^ (2 ^ k)), hfac, mul_eq_zero, Finset.prod_eq_zero_iff]
  constructor
  · rintro (hab | ⟨j, hj, hfj⟩)
    · exact Or.inl (sub_eq_zero.mp hab)
    · exact Or.inr ⟨j, hj, by linear_combination hfj⟩
  · rintro (hab | ⟨j, hj, hfj⟩)
    · exact Or.inl (by rw [hab]; ring)
    · exact Or.inr ⟨j, hj, by linear_combination hfj⟩

end ArkLib.ProximityGap.TwoPowerTower

#print axioms ArkLib.ProximityGap.TwoPowerTower.pow_two_pow_sub_eq
#print axioms ArkLib.ProximityGap.TwoPowerTower.pow_two_pow_eq_iff
