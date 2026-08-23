/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Degree Calculus for Rational Functions

This module establishes a *degree calculus* for the field of rational functions $\mathbb{F}(X)$
(represented in Mathlib via `RatFunc 𝔽`). It tracks the propagation of algebraic complexity
under field operations. This calculus is key for bounding coefficient degrees in iterative
constructions, such as the Hensel lifting process in [BCIKS20] Appendix A.4, where rational
functions are subjected to addition, multiplication, inversion, and power operations.

## Definitions and Measures

We analyze two distinct notions of degree:

1. **Additive Degree (`RatFunc.intDegree`)**:
   Defined as $\text{intDegree}(p/q) = \deg(p) - \deg(q)$. This measure behaves cleanly under
   multiplicative operations
   ($\text{intDegree}(f \cdot g) = \text{intDegree}(f) + \text{intDegree}(g)$)
   and satisfies subadditivity under addition.

2. **Structural Size Measure (`zDeg`)**:
   Defined as $\text{zDeg}(p/q) = \max(\deg(p), \deg(q))$ for $p, q$ coprime.
   This captures the maximum degree of the polynomial components in the reduced representation,
   serving as a proxy for the space/computational complexity of the rational function.

We prove the core subadditivity and submultiplicativity properties of $\text{zDeg}$:
* Sum: $\text{zDeg}(f + g) \le \text{zDeg}(f) + \text{zDeg}(g)$
* Product: $\text{zDeg}(f \cdot g) \le \text{zDeg}(f) + \text{zDeg}(g)$
* Inverse: $\text{zDeg}(f^{-1}) = \text{zDeg}(f)$
* Power: $\text{zDeg}(f^n) \le n \cdot \text{zDeg}(f)$
-/

namespace ArkLib

open Polynomial RatFunc

noncomputable section

variable {F : Type*} [Field F]

/-! ### `intDegree` corollaries (reusing mathlib)

Mathlib already proves the heavy lifting for `RatFunc.intDegree`:
`RatFunc.intDegree_mul`, `RatFunc.intDegree_inv`, `RatFunc.intDegree_add_le`,
`RatFunc.intDegree_C`, `RatFunc.intDegree_polynomial`, … .  We restate two convenient
corollaries used by the Hensel recursion. -/

/-- The `intDegree` of a constant (image of a field element) is `0`. -/
theorem intDegree_algebraMap_field (c : F) :
    (algebraMap F (RatFunc F) c).intDegree = 0 := by
  -- `algebraMap F (RatFunc F) c = RatFunc.C c`, whose `intDegree` is `0`.
  simp

/-- `intDegree` is additive under powers (for nonzero base): `intDegree (a ^ n) = n • intDegree a`.
This is the exact propagation rule for the multiplicative part of the Hensel recursion. -/
theorem intDegree_pow {a : RatFunc F} (ha : a ≠ 0) (n : ℕ) :
    (a ^ n).intDegree = n * a.intDegree := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hak : a ^ k ≠ 0 := pow_ne_zero k ha
      rw [pow_succ, RatFunc.intDegree_mul hak ha, ih]
      push_cast
      ring

/-! ### The `zDeg` size measure -/

/-- `zDeg r` is the *size* of the reduced representation of `r`, namely the maximum of the
`natDegree`s of its numerator and denominator.  For `r = p/q` in lowest terms,
`zDeg r = max (deg p) (deg q)`; this is the quantity one must bound to control the storage cost of
a rational function during the BCIKS20 Hensel lifting. -/
def zDeg (r : RatFunc F) : ℕ := max r.num.natDegree r.denom.natDegree

theorem zDeg_def (r : RatFunc F) : zDeg r = max r.num.natDegree r.denom.natDegree := rfl

theorem num_natDegree_le_zDeg (r : RatFunc F) : r.num.natDegree ≤ zDeg r := le_max_left _ _

theorem denom_natDegree_le_zDeg (r : RatFunc F) : r.denom.natDegree ≤ zDeg r := le_max_right _ _

@[simp]
theorem zDeg_zero : zDeg (0 : RatFunc F) = 0 := by
  simp [zDeg, RatFunc.num_zero, RatFunc.denom_zero]

@[simp]
theorem zDeg_one : zDeg (1 : RatFunc F) = 0 := by
  simp [zDeg, RatFunc.num_one, RatFunc.denom_one]

/-- The size of a constant (image of a field element under `algebraMap`) is `0`. -/
@[simp]
theorem zDeg_algebraMap (c : F) : zDeg (algebraMap F (RatFunc F) c) = 0 := by
  -- `algebraMap F (RatFunc F) = (RatFunc.C : F → RatFunc F)` on field elements.
  have : algebraMap F (RatFunc F) c = RatFunc.C c := rfl
  rw [this, zDeg, RatFunc.num_C, RatFunc.denom_C, Polynomial.natDegree_C,
    Polynomial.natDegree_one, max_self]

/-- The size of a polynomial constant `RatFunc.C c` is `0`. -/
@[simp]
theorem zDeg_C (c : F) : zDeg (RatFunc.C c) = 0 := by
  rw [zDeg, RatFunc.num_C, RatFunc.denom_C, Polynomial.natDegree_C, Polynomial.natDegree_one,
    max_self]

/-! #### Multiplication -/

/-- Submultiplicativity of `zDeg`: `zDeg (a * b) ≤ zDeg a + zDeg b`.

The proof uses the mathlib divisibility facts `RatFunc.num_mul_dvd` and `RatFunc.denom_mul_dvd`
together with `Polynomial.natDegree_le_of_dvd`. -/
theorem zDeg_mul_le (a b : RatFunc F) : zDeg (a * b) ≤ zDeg a + zDeg b := by
  rw [zDeg, max_le_iff]
  constructor
  · -- numerator side: `num (a*b) ∣ num a * num b`
    have hdvd : (a * b).num ∣ a.num * b.num := RatFunc.num_mul_dvd a b
    by_cases hab : a * b = 0
    · simp [hab]
    · have hne : a.num * b.num ≠ 0 := by
        have ha : a ≠ 0 := left_ne_zero_of_mul hab
        have hb : b ≠ 0 := right_ne_zero_of_mul hab
        exact mul_ne_zero (RatFunc.num_ne_zero ha) (RatFunc.num_ne_zero hb)
      calc (a * b).num.natDegree ≤ (a.num * b.num).natDegree :=
              Polynomial.natDegree_le_of_dvd hdvd hne
        _ ≤ a.num.natDegree + b.num.natDegree := Polynomial.natDegree_mul_le
        _ ≤ zDeg a + zDeg b :=
              Nat.add_le_add (num_natDegree_le_zDeg a) (num_natDegree_le_zDeg b)
  · -- denominator side: `denom (a*b) ∣ denom a * denom b`, RHS always nonzero
    have hdvd : (a * b).denom ∣ a.denom * b.denom := RatFunc.denom_mul_dvd a b
    have hne : a.denom * b.denom ≠ 0 :=
      mul_ne_zero (RatFunc.denom_ne_zero a) (RatFunc.denom_ne_zero b)
    calc (a * b).denom.natDegree ≤ (a.denom * b.denom).natDegree :=
            Polynomial.natDegree_le_of_dvd hdvd hne
      _ ≤ a.denom.natDegree + b.denom.natDegree := Polynomial.natDegree_mul_le
      _ ≤ zDeg a + zDeg b :=
            Nat.add_le_add (denom_natDegree_le_zDeg a) (denom_natDegree_le_zDeg b)

/-! #### Addition -/

/-- The common-denominator identity for `RatFunc F`: writing `a` and `b` over their reduced
denominators and combining the fractions, `a + b` equals
`(a.num * b.denom + a.denom * b.num) / (a.denom * b.denom)` as images of polynomials. -/
theorem add_eq_combined_div (a b : RatFunc F) :
    a + b
      = algebraMap F[X] (RatFunc F) (a.num * b.denom + a.denom * b.num)
          / algebraMap F[X] (RatFunc F) (a.denom * b.denom) := by
  conv_lhs => rw [← RatFunc.num_div_denom a, ← RatFunc.num_div_denom b]
  rw [div_add_div _ _ (algebraMap_ne_zero (RatFunc.denom_ne_zero a))
        (algebraMap_ne_zero (RatFunc.denom_ne_zero b)),
    map_add, map_mul, map_mul, map_mul]

/-- The numerator of a sum divides the "common denominator" combination
`a.num * b.denom + a.denom * b.num`, provided the sum is nonzero.

This is the additive analogue of `RatFunc.num_mul_dvd` and is the key step for the addition
bound; it is not in mathlib so we prove it via `RatFunc.num_dvd`. -/
theorem num_add_dvd {a b : RatFunc F}
    (hp : a.num * b.denom + a.denom * b.num ≠ 0) :
    (a + b).num ∣ a.num * b.denom + a.denom * b.num := by
  rw [RatFunc.num_dvd hp]
  refine ⟨a.denom * b.denom, mul_ne_zero (RatFunc.denom_ne_zero a) (RatFunc.denom_ne_zero b),
    add_eq_combined_div a b⟩

/-- Subadditivity of `zDeg`: `zDeg (a + b) ≤ zDeg a + zDeg b`. -/
theorem zDeg_add_le (a b : RatFunc F) : zDeg (a + b) ≤ zDeg a + zDeg b := by
  by_cases hab : a + b = 0
  · simp [hab]
  rw [zDeg, max_le_iff]
  -- A uniform bound `m := zDeg a + zDeg b` on both `a.num * b.denom` and `a.denom * b.num`.
  have hbound₁ : (a.num * b.denom).natDegree ≤ zDeg a + zDeg b :=
    le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add (num_natDegree_le_zDeg a) (denom_natDegree_le_zDeg b))
  have hbound₂ : (a.denom * b.num).natDegree ≤ zDeg a + zDeg b :=
    le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add (denom_natDegree_le_zDeg a) (num_natDegree_le_zDeg b))
  constructor
  · -- numerator side
    by_cases hp : a.num * b.denom + a.denom * b.num = 0
    · -- then `num (a+b) = 0`, since `a + b = p / (denom a * denom b)` with `p = 0`.
      have hsum : a + b = 0 := by
        rw [add_eq_combined_div a b, hp, map_zero, zero_div]
      exact absurd hsum hab
    · have hdvd : (a + b).num ∣ a.num * b.denom + a.denom * b.num := num_add_dvd hp
      calc (a + b).num.natDegree
            ≤ (a.num * b.denom + a.denom * b.num).natDegree :=
              Polynomial.natDegree_le_of_dvd hdvd hp
        _ ≤ max (a.num * b.denom).natDegree (a.denom * b.num).natDegree :=
              Polynomial.natDegree_add_le _ _
        _ ≤ zDeg a + zDeg b := max_le hbound₁ hbound₂
  · -- denominator side: `denom (a+b) ∣ denom a * denom b`
    have hdvd : (a + b).denom ∣ a.denom * b.denom := RatFunc.denom_add_dvd a b
    have hne : a.denom * b.denom ≠ 0 :=
      mul_ne_zero (RatFunc.denom_ne_zero a) (RatFunc.denom_ne_zero b)
    calc (a + b).denom.natDegree ≤ (a.denom * b.denom).natDegree :=
            Polynomial.natDegree_le_of_dvd hdvd hne
      _ ≤ a.denom.natDegree + b.denom.natDegree := Polynomial.natDegree_mul_le
      _ ≤ zDeg a + zDeg b :=
            Nat.add_le_add (denom_natDegree_le_zDeg a) (denom_natDegree_le_zDeg b)

/-- The weaker, explicitly-requested addition bound
`zDeg (a + b) ≤ max (zDeg a) (zDeg b) + zDeg b`, an immediate consequence of `zDeg_add_le`. -/
theorem zDeg_add_le' (a b : RatFunc F) : zDeg (a + b) ≤ max (zDeg a) (zDeg b) + zDeg b :=
  le_trans (zDeg_add_le a b) (Nat.add_le_add_right (le_max_left _ _) _)

/-! #### Inversion -/

/-- The size measure is invariant under inversion: `zDeg a⁻¹ = zDeg a`.

Inversion swaps numerator and denominator up to a unit (`RatFunc.associated_num_inv` /
`RatFunc.associated_denom_inv`); associated polynomials have equal `natDegree`. -/
@[simp]
theorem zDeg_inv (a : RatFunc F) : zDeg a⁻¹ = zDeg a := by
  by_cases ha : a = 0
  · simp [ha]
  · -- `num a⁻¹` is associated to `denom a`, and `denom a⁻¹` to `num a`.
    have h1 : (a⁻¹).num.natDegree = a.denom.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated (RatFunc.associated_num_inv ha))
    have h2 : (a⁻¹).denom.natDegree = a.num.natDegree :=
      Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_eq_degree_of_associated (RatFunc.associated_denom_inv ha))
    rw [zDeg, zDeg, h1, h2, max_comm]

/-! #### Powers -/

/-- Powers grow the size measure at most linearly: `zDeg (a ^ n) ≤ n * zDeg a`. -/
theorem zDeg_pow_le (a : RatFunc F) (n : ℕ) : zDeg (a ^ n) ≤ n * zDeg a := by
  induction n with
  | zero => simp
  | succ k ih =>
      calc zDeg (a ^ (k + 1)) = zDeg (a ^ k * a) := by rw [pow_succ]
        _ ≤ zDeg (a ^ k) + zDeg a := zDeg_mul_le _ _
        _ ≤ k * zDeg a + zDeg a := Nat.add_le_add_right ih _
        _ = (k + 1) * zDeg a := by ring

/-- `zpow` (integer power) of a nonzero rational function grows the size measure linearly in `|n|`:
`zDeg (a ^ n) ≤ n.natAbs * zDeg a`.  Combines `zDeg_pow_le` with `zDeg_inv`. -/
theorem zDeg_zpow_le {a : RatFunc F} (n : ℤ) : zDeg (a ^ n) ≤ n.natAbs * zDeg a := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Int.natAbs_natCast]
    exact zDeg_pow_le a m
  · rw [zpow_neg, zpow_natCast, zDeg_inv, Int.natAbs_neg, Int.natAbs_natCast]
    exact zDeg_pow_le a m

end

/-! ### Axiom audit

Every main lemma must depend only on `[propext, Classical.choice, Quot.sound]`. -/

#print axioms intDegree_algebraMap_field
#print axioms intDegree_pow
#print axioms zDeg_zero
#print axioms zDeg_one
#print axioms zDeg_algebraMap
#print axioms zDeg_C
#print axioms zDeg_mul_le
#print axioms add_eq_combined_div
#print axioms num_add_dvd
#print axioms zDeg_add_le
#print axioms zDeg_add_le'
#print axioms zDeg_inv
#print axioms zDeg_pow_le
#print axioms zDeg_zpow_le

end ArkLib
