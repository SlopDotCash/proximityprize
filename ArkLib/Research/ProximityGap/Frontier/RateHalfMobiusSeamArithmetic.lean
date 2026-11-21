/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Proximity Prize contributors
-/
import Init.Data.Nat.PowMod

/-! # Finite arithmetic of the three rate-half pair-intersection polynomials

The three quadratic coefficient rows and fractional-linear maps in the companion
`docs/research/proximity-gap/rate-half-mobius-seams.md` are computed directly from
the first prize prime and generator. These declarations certify the field residues
and counting parameters. The general polynomial and MCA arguments are in the note.
-/

namespace ProximityGap.RateHalfMobiusSeamArithmetic

/-- First sponsor modulus. -/
def p : Nat := 365375409332725729550921208179070755120141565953

/-- First sponsor generator of the length-`2 ^ 30` evaluation group. -/
def g : Nat := 303645430271030343624574566109998498685964493478

/-- Natural-number representative of subtraction modulo `p`. -/
def subMod (a b : Nat) := (a % p + p - b % p) % p

structure Triple where
  x : Nat
  y : Nat
  z : Nat

structure Matrix where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

def locator (u v : Nat) : Triple :=
  ⟨u * v % p, subMod 0 (u + v), 1⟩

def cross (r s : Triple) : Triple :=
  ⟨subMod (r.y * s.z) (r.z * s.y), subMod (r.z * s.x) (r.x * s.z),
   subMod (r.x * s.y) (r.y * s.x)⟩

def direction (r : Triple) : Matrix := ⟨subMod 0 r.x, r.y, subMod 0 r.y, r.z⟩

def det (m : Matrix) := subMod (m.a * m.d) (m.b * m.c)

def relative (v w : Matrix) : Matrix :=
  ⟨subMod (w.d * v.a) (w.b * v.c), subMod (w.d * v.b) (w.b * v.d),
   subMod (w.a * v.c) (w.c * v.a), subMod (w.a * v.d) (w.c * v.b)⟩

def full (m : Matrix) := [m.a, m.b, m.c, m.d].all (· != 0)

def evalPair (m : Matrix) (x : Nat) : Nat × Nat :=
  ((m.a*x + m.b) % p, (m.c*x + m.d) % p)

def eqDirection (x y : Nat × Nat) := x.1*y.2 % p == x.2*y.1 % p

def v0 := Nat.powMod g 0 p
def v1 := Nat.powMod g 1 p
def v3 := Nat.powMod g 3 p
def v6 := Nat.powMod g 6 p
def v10 := Nat.powMod g 10 p
def v15 := Nat.powMod g 15 p
def l0 := locator v0 v1
def l1 := locator v3 v6
def l2 := locator v10 v15
def m0 := direction (cross l1 l2)
def m1 := direction (cross l2 l0)
def m2 := direction (cross l0 l1)

/-- Distinct roots, nonsingular coefficient basis, nonsingular individual maps
and all three relative maps with four nonzero coefficients. -/
theorem production_matrix_certificate :
    [v0, v1, v3, v6, v10, v15].Nodup ∧
    (l0.x * (cross l1 l2).x + l0.y * (cross l1 l2).y + l0.z * (cross l1 l2).z) % p ≠ 0 ∧
    [m0, m1, m2].all (fun m => det m != 0) = true ∧
    [relative m0 m1, relative m0 m2, relative m1 m2].all full = true := by decide

def seams : List (Nat × Nat) :=
  [evalPair m1 v0, evalPair m1 v1, evalPair m2 v3,
   evalPair m2 v6, evalPair m0 v10, evalPair m0 v15]

def other : List (Nat × Nat) :=
  [evalPair m2 v0, evalPair m2 v1, evalPair m0 v3,
   evalPair m0 v6, evalPair m1 v10, evalPair m1 v15]

/-- On each of the six pair intersections the remaining maps give the same finite
projective direction, and the six directions are pairwise distinct. -/
theorem production_seam_certificate :
    (seams ++ other).all (fun x => x.2 != 0) = true ∧
    (seams.zipWith eqDirection other).all id = true ∧
    seams.Pairwise (fun x y => eqDirection x y = false) := by decide

/-- Linear dimension, sparse-support, derivative and root-count budgets for the
explicit Stepanov construction. -/
theorem production_intersection_arithmetic :
    2048 * 4096 + 2048 * 2047 < 4096 * 64 * 64 ∧
    4096 * 64 ≤ 2 ^ 30 ∧ 4095 + 63 * 2 ^ 30 < p ∧ 2048 < p ∧
    (4095 + 126 * 2 ^ 30) / 2048 = 66060289 ∧
    2 ^ 30 - 6 * 66060289 - 27 = 677380063 ∧ 3 * 178956970 ≤ 677380063 := by decide

/-- Block sizes, agreement cardinality, event budget and strict sub-one-third radius. -/
theorem production_witness_arithmetic :
    6 * 178956970 + 4 = 2 ^ 30 ∧ 3 * 178956970 - 2 + 3 < 2 ^ 29 ∧
    2 ^ 29 ≤ 4 * 178956970 + 2 ∧ 4 * 178956970 + 3 + 357913941 = 2 ^ 30 ∧
    3 * 357913941 < 2 ^ 30 ∧ 6 * 178956970 + 6 = 2 ^ 30 + 2 ∧
    p < (2 ^ 30 + 2) * 2 ^ 128 := by decide

#print axioms production_matrix_certificate
#print axioms production_seam_certificate
#print axioms production_intersection_arithmetic
#print axioms production_witness_arithmetic

end ProximityGap.RateHalfMobiusSeamArithmetic
