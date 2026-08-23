/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Image

/-!
# Fin-indexed `Finsupp` insertion/removal helpers

Thin wrappers around `Fin.insertNth` and `Fin.removeNth` for finitely supported functions whose
domain is finite.
-/

namespace Finsupp

variable {n : ℕ}

/-- Insert one coordinate into a finitely supported tuple indexed by `Fin`. -/
noncomputable def insertNth (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) :
    Fin (n + 1) →₀ ℕ :=
  onFinset Finset.univ (Fin.insertNth p i m) (fun _ _ => Finset.mem_univ _)

/-- Remove one coordinate from a finitely supported tuple indexed by `Fin`. -/
noncomputable def removeNth (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) :
    Fin n →₀ ℕ :=
  onFinset Finset.univ (p.removeNth m) (fun _ _ => Finset.mem_univ _)

@[simp]
theorem insertNth_apply_same (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) :
    insertNth p i m p = i := by
  simp [insertNth]

@[simp]
theorem insertNth_apply_succAbove (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) (j : Fin n) :
    insertNth p i m (p.succAbove j) = m j := by
  simp [insertNth]

@[simp]
theorem removeNth_apply (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) (j : Fin n) :
    removeNth p m j = m (p.succAbove j) := by
  simp [removeNth, Fin.removeNth_apply]

@[simp]
theorem insertNth_update_removeNth (p : Fin (n + 1)) (i : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    insertNth p i (removeNth p m) = Function.update m p i := by
  ext j
  refine Fin.succAboveCases p ?_ ?_ j
  · simp
  · intro k
    simp

@[simp]
theorem insertNth_removeNth (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) :
    insertNth p (m p) (removeNth p m) = m := by
  ext j
  refine Fin.succAboveCases p ?_ ?_ j
  · simp
  · intro k
    simp

theorem insertNth_self_removeNth (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) :
    insertNth p (m p) (removeNth p m) = m :=
  insertNth_removeNth p m

theorem insertNth_right_injective (p : Fin (n + 1)) {i : ℕ} :
    Function.Injective (insertNth p i : (Fin n →₀ ℕ) → Fin (n + 1) →₀ ℕ) := by
  intro m₁ m₂ h
  ext j
  simpa using congrFun (congrArg DFunLike.coe h) (p.succAbove j)

theorem sum_insertNth (m : Fin n →₀ ℕ) (i : ℕ) (p : Fin (n + 1)) :
    (insertNth p i m).sum (fun _ e => e) = m.sum (fun _ e => e) + i := by
  rw [sum_fintype, sum_fintype]
  · rw [Fin.sum_univ_succAbove _ p]
    simp [add_comm]
  · simp
  · simp

end Finsupp

export Finsupp (sum_insertNth)
