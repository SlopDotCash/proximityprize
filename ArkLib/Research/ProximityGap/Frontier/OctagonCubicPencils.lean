/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Three, three and two points in fibers of a cubic pencil on an octagon

For a primitive eighth root, fix a leftover pair of exponents `0,d`. Partition the
other six into two triples. The determinant tests whether the ratio of their
monic cubic locators takes equal values at the leftover pair. Its cyclotomic
norm singles out exactly characteristics 3, 17 and 31.
-/

namespace ProximityGap.OctagonCubicPencils

set_option autoImplicit false
open Finset

/-- Coefficients in the power basis modulo `X^4 + 1`. -/
structure Quartic where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace Quartic

def sub (u v : Quartic) : Quartic :=
  ⟨u.a-v.a, u.b-v.b, u.c-v.c, u.d-v.d⟩

def mul (u v : Quartic) : Quartic :=
  ⟨u.a*v.a-u.b*v.d-u.c*v.c-u.d*v.b,
   u.a*v.b+u.b*v.a-u.c*v.d-u.d*v.c,
   u.a*v.c+u.b*v.b+u.c*v.a-u.d*v.d,
   u.a*v.d+u.b*v.c+u.c*v.b+u.d*v.a⟩

def norm (u : Quartic) : ℤ :=
  (u.a^2-u.c^2+2*u.b*u.d)^2 + (2*u.a*u.c-u.b^2+u.d^2)^2

def eval {F : Type*} [Field F] (z : F) (u : Quartic) : F :=
  u.a + u.b*z + u.c*z^2 + u.d*z^3

theorem eval_sub {F : Type*} [Field F] (z : F) (u v : Quartic) :
    eval z (sub u v) = eval z u - eval z v := by
  simp only [eval, sub, Int.cast_sub]
  ring

private theorem powers {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) :
    z^5 = -z ∧ z^6 = -z^2 ∧ z^7 = -z^3 := by
  constructor
  · rw [pow_succ, hz, neg_one_mul]
  constructor
  · rw [show 6 = 4+2 by decide, pow_add, hz, neg_one_mul]
  · rw [show 7 = 4+3 by decide, pow_add, hz, neg_one_mul]

theorem eval_mul {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) (u v : Quartic) :
    eval z (mul u v) = eval z u * eval z v := by
  simp only [eval, mul, Int.cast_sub, Int.cast_add, Int.cast_mul]
  ring_nf
  rw [hz, (powers hz).1, (powers hz).2.1]
  ring

private theorem paired {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) (u : Quartic) :
    eval z u * eval (-z) u =
      ((u.a:F)^2-u.c^2+2*u.b*u.d) + (2*(u.a:F)*u.c-u.b^2+u.d^2)*z^2 := by
  simp only [eval]
  ring_nf
  rw [hz, (powers hz).2.1]
  ring

/-- The four conjugate determinants multiply to the computed integer norm. -/
theorem norm_eq {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) (u : Quartic) :
    (u.norm : F) = (eval z u * eval (-z) u) * (eval (z^3) u * eval (-(z^3)) u) := by
  have hc : (z^3)^4 = -1 := by
    rw [← pow_mul, show 3*4=4*3 by decide, pow_mul, hz]
    norm_num
  rw [paired hz, paired hc, ← pow_mul, (powers hz).2.1]
  simp only [norm, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring_nf
  rw [hz]
  ring

end Quartic

def root (i : ℕ) : Quartic :=
  match i with
  | 0 => ⟨1,0,0,0⟩
  | 1 => ⟨0,1,0,0⟩
  | 2 => ⟨0,0,1,0⟩
  | 3 => ⟨0,0,0,1⟩
  | 4 => ⟨-1,0,0,0⟩
  | 5 => ⟨0,-1,0,0⟩
  | 6 => ⟨0,0,-1,0⟩
  | _ => ⟨0,0,0,-1⟩

theorem eval_root {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) (i : ℕ) (hi : i < 8) :
    Quartic.eval z (root i) = z^i := by
  obtain ⟨h₅, h₆, h₇⟩ := Quartic.powers hz
  interval_cases i <;> simp [root, Quartic.eval, hz, h₅, h₆, h₇]

/-- Evaluate a monic locator on an octagon site in the integral power basis. -/
def atSite (i : ℕ) : List ℕ → Quartic
  | [] => ⟨1,0,0,0⟩
  | j :: js => ((root i).sub (root j)).mul (atSite i js)

theorem eval_atSite {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1)
    (i : ℕ) (hi : i < 8) (sites : List ℕ) (hs : ∀ j ∈ sites, j < 8) :
    Quartic.eval z (atSite i sites) = (sites.map (fun j => z^i-z^j)).prod := by
  induction sites with
  | nil => simp [atSite, Quartic.eval]
  | cons x xs ih =>
    simp only [atSite, Quartic.eval_mul hz, Quartic.eval_sub, List.map_cons, List.prod_cons]
    rw [eval_root hz i hi, eval_root hz x (hs _ (by simp)), ih (fun j hj => hs j (by simp [hj]))]

def remaining (d : ℕ) := ((range 8).erase 0).erase d

/-- Cross product of the two cubic values at each of the two remaining sites. -/
def det (d : ℕ) (A : Finset ℕ) : Quartic :=
  let B := (List.range 8).filter (fun j => j ∈ remaining d ∧ j ∉ A)
  let S := (List.range 8).filter (fun j => j ∈ A)
  ((atSite 0 S).mul (atSite d B)).sub ((atSite d S).mul (atSite 0 B))

def norms : Finset ℤ :=
  ((range 8).erase 0).biUnion fun d =>
    ((remaining d).powersetCard 3).image fun A => (det d A).norm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Evaluate the integral norms of all normalized octagon partitions.
theorem norm_values : norms = {256,1024,4096,16384,18496,20736,65536,73984,246016,331776} := by
  decide +kernel

/-- A normalized partition has zero determinant for one of the four primitive
root choices exactly in the three exceptional odd characteristics. -/
theorem exceptional {F : Type*} [Field F] {z : F} (hz : z ^ 4 = -1) (h2 : (2 : F) ≠ 0) :
    (∃ d ∈ (range 8).erase 0, ∃ A ∈ (remaining d).powersetCard 3,
      Quartic.eval z (det d A) = 0 ∨ Quartic.eval (-z) (det d A) = 0 ∨
      Quartic.eval (z^3) (det d A) = 0 ∨ Quartic.eval (-(z^3)) (det d A) = 0) ↔
    (3:F) = 0 ∨ (17:F) = 0 ∨ (31:F) = 0 := by
  have toNorm (u : Quartic) : (u.norm : F) = 0 ↔
      Quartic.eval z u = 0 ∨ Quartic.eval (-z) u = 0 ∨
      Quartic.eval (z^3) u = 0 ∨ Quartic.eval (-(z^3)) u = 0 := by
    rw [Quartic.norm_eq hz]
    simp only [mul_eq_zero, or_assoc]
  have criterion : (∃ k ∈ norms, (k:F) = 0) ↔
      (3:F) = 0 ∨ (17:F) = 0 ∨ (31:F) = 0 := by
    rw [norm_values]
    simp only [Finset.exists_mem_insert, Finset.mem_singleton, exists_eq_left, Int.cast_ofNat]
    rw [show (256:F) = 2^8 by norm_num, show (1024:F) = 2^10 by norm_num,
      show (4096:F) = 2^12 by norm_num, show (16384:F) = 2^14 by norm_num,
      show (18496:F) = 2^6*17^2 by norm_num, show (20736:F) = 2^8*3^4 by norm_num,
      show (65536:F) = 2^16 by norm_num, show (73984:F) = 2^8*17^2 by norm_num,
      show (246016:F) = 2^8*31^2 by norm_num, show (331776:F) = 2^12*3^4 by norm_num]
    simp [h2, mul_eq_zero, or_comm, or_left_comm]
  rw [← criterion]
  constructor
  · rintro ⟨d, hd, A, hA, h⟩
    exact ⟨_, mem_biUnion.mpr ⟨d, hd, mem_image.mpr ⟨A, hA, rfl⟩⟩, (toNorm _).mpr h⟩
  · rintro ⟨k, hk, hzero⟩
    obtain ⟨d, hd, himg⟩ := mem_biUnion.mp hk
    obtain ⟨A, hA, rfl⟩ := mem_image.mp himg
    exact ⟨d, hd, A, hA, (toNorm _).mp hzero⟩

#print axioms eval_atSite
#print axioms exceptional

end ProximityGap.OctagonCubicPencils
