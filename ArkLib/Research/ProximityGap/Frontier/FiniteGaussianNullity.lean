/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-! # Executable nullity of a finite system of linear equations

Eliminate variables from the left. A zero column leaves its variable free.
A nonzero pivot determines its variable uniquely from the remaining ones.
Every reduced row is materialized to avoid repeated evaluation of earlier eliminations.
-/

namespace ProximityGap.FiniteGaussianNullity

variable {K : Type*} [Field K] [DecidableEq K] {d : ℕ}

/-- Cache a finite row in a vector, with constant-time access to its entries. -/
def cache (r : Fin d → K) : Fin d → K :=
  let a := Vector.ofFn r
  fun j => a[j.val]

omit [Field K] [DecidableEq K] in
@[simp] private theorem cache_apply (r : Fin d → K) (j : Fin d) : cache r j = r j := by
  simp [cache]

omit [Field K] [DecidableEq K] in
@[simp] private theorem cache_eq (r : Fin d → K) : cache r = r := funext (cache_apply r)

/-- Drop a column whose entries are already zero. -/
abbrev tail (r : Fin (d + 1) → K) : Fin d → K := Fin.tail r

/-- Subtract a multiple of the pivot equation and discard the eliminated column. -/
def reduce (p r : Fin (d + 1) → K) : Fin d → K :=
  let c := r 0 / p 0
  cache fun j => r j.succ - c * p j.succ

/-- Gaussian nullity for a list of rows, using field operations and zero tests. -/
def nullity : (d : ℕ) → List (Fin d → K) → ℕ
  | 0, _ => 0
  | d + 1, rows =>
    match rows.find? (fun r => decide (r 0 ≠ 0)) with
    | none => nullity d (rows.map fun r => cache (tail r)) + 1
    | some p => nullity d (rows.map (reduce p))

/-- Pair a row with a coefficient vector. -/
def dot (r x : Fin d → K) : K := ∑ j, r j * x j

/-- All homogeneous solutions to the actual input row list. -/
def Solutions (rows : List (Fin d → K)) := {x : Fin d → K // ∀ r ∈ rows, dot r x = 0}

instance (rows : List (Fin d → K)) [Finite K] : Finite (Solutions rows) :=
  Subtype.finite

omit [DecidableEq K] in
private theorem dot_split (r x : Fin (d + 1) → K) :
    dot r x = r 0 * x 0 + dot (tail r) (tail x) := by
  simp [dot, Fin.sum_univ_succ, tail, Fin.tail]

omit [DecidableEq K] in
private theorem dot_cons (r : Fin (d + 1) → K) (x : Fin d → K) (c : K) :
    dot r (Fin.cons c x) = r 0 * c + dot (tail r) x := by
  rw [dot_split]
  simp [tail]

omit [DecidableEq K] in
private theorem dot_reduce (p r : Fin (d + 1) → K) (x : Fin d → K) :
    dot (reduce p r) x = dot (tail r) x - (r 0 / p 0) * dot (tail p) x := by
  simp [dot, reduce, tail, Fin.tail, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

omit [DecidableEq K] in
private theorem clear_eq (p r : Fin (d + 1) → K) (hp : p 0 ≠ 0) (x : Fin d → K) :
    dot r (Fin.cons (-(dot (tail p) x) / p 0) x) = dot (reduce p r) x := by
  rw [dot_cons, dot_reduce]
  field_simp
  ring

private def noPivotEquiv (rows : List (Fin (d + 1) → K)) (h : ∀ r ∈ rows, r 0 = 0) :
    Solutions rows ≃ K × Solutions (rows.map fun r => cache (tail r)) where
  toFun x := ⟨x.val 0, ⟨tail x.val, by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    simpa [dot_split a x.val, h a ha] using x.property a ha⟩⟩
  invFun v := ⟨Fin.cons v.1 v.2.val, by
    intro r hr
    have hrow := v.2.property _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
    rw [dot_cons, h r hr, zero_mul, zero_add]
    simpa using hrow⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv v := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext j
      simp [tail]

private def pivotEquiv (rows : List (Fin (d + 1) → K)) (p : Fin (d + 1) → K) (hpr : p ∈ rows)
    (hp : p 0 ≠ 0) :
    Solutions rows ≃ Solutions (rows.map (reduce p)) where
  toFun x := ⟨tail x.val, by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [← clear_eq p a hp]
    have head := x.property p hpr
    rw [dot_split] at head
    have hh : -(dot (tail p) (tail x.val)) / p 0 = x.val 0 := by
      apply (div_eq_iff hp).mpr
      linear_combination -head
    simpa [hh, tail] using x.property a ha⟩
  invFun x := ⟨Fin.cons (-(dot (tail p) x.val) / p 0) x.val, by
    intro r hr
    rw [clear_eq p r hp]
    exact x.property _ (List.mem_map.mpr ⟨r,hr,rfl⟩)⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]
      have h := x.property p hpr
      rw [dot_split] at h
      apply (div_eq_iff hp).mpr
      linear_combination -h
    · rfl
  right_inv x := by
    apply Subtype.ext
    funext j
    simp [tail]

/-- Each Gaussian nullity is the exponent in the exact count of solutions. -/
theorem card_solutions [Fintype K] (d : ℕ) (rows : List (Fin d → K)) :
    Nat.card (Solutions rows) = Fintype.card K ^ nullity d rows := by
  induction d with
  | zero =>
    let _ : Subsingleton (Solutions rows) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
    let _ : Nonempty (Solutions rows) := ⟨⟨0, by simp [dot]⟩⟩
    simp [nullity]
  | succ d ih =>
    unfold nullity
    split
    next he =>
      have h : ∀ r ∈ rows, r 0 = 0 := by simpa using List.find?_eq_none.mp he
      rw [Nat.card_congr (noPivotEquiv rows h), Nat.card_prod, ih, Nat.card_eq_fintype_card,
        pow_succ, Nat.mul_comm]
    next p he =>
      have hp : p 0 ≠ 0 := by simpa using List.find?_some he
      rw [Nat.card_congr (pivotEquiv rows p (List.mem_of_find?_eq_some he) hp), ih]

end ProximityGap.FiniteGaussianNullity

#print axioms ProximityGap.FiniteGaussianNullity.card_solutions
