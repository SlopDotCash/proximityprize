/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card

/-!
# G249: Cartesian discrepancy does not select quotient-Jacobi rows (#466)

The Lu--Zheng--Zheng/Jacobi-distribution route controls a two-dimensional Cartesian character
family.  G228/G248 need a fixed second-character row, followed by a rank-dependent arithmetic
weight.  This file records the sharp information-theoretic obstruction in its smallest finite form.

A global exceptional set occupying only one row has density exactly `1/m` in an `m × m` Cartesian
family, but that row is completely uncontrolled.  Therefore any route that turns a Cartesian
exception budget into uniform row control must beat the row density threshold `D < 1/m`.  The
published Jacobi discrepancy at the sponsor parameters misses that threshold by 113--114 bits
(G248 probe), so it cannot supply the CORE rowwise weighted covariance.

This is a route no-go, not a Jacobi estimate and not a prize closure.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G249CartesianRowSelectionBarrier

open Finset

/-- The distinguished zeroth row in an `(m+1) × (m+1)` Cartesian family. -/
def rowZero (m : ℕ) : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩

/-- A one-row exceptional set: all pairs whose first coordinate is `rowZero`. -/
def rowBad (m : ℕ) : Finset (Fin (m + 1) × Fin (m + 1)) :=
  (Finset.univ : Finset (Fin (m + 1))).image (fun j => (rowZero m, j))

/-- The one-row exceptional set has exactly one row's worth of points. -/
theorem rowBad_card (m : ℕ) : (rowBad m).card = m + 1 := by
  unfold rowBad
  rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
  simp

/-- Every point of the distinguished row is exceptional. -/
theorem rowBad_contains_full_row (m : ℕ) (j : Fin (m + 1)) :
    (rowZero m, j) ∈ rowBad m := by
  unfold rowBad
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- No other row is present in the one-row exceptional set. -/
theorem mem_rowBad_iff_first_eq_rowZero (m : ℕ) (x : Fin (m + 1) × Fin (m + 1)) :
    x ∈ rowBad m ↔ x.1 = rowZero m := by
  constructor
  · intro hx
    unfold rowBad at hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    rfl
  · intro hx
    rcases x with ⟨i, j⟩
    dsimp at hx
    subst i
    exact rowBad_contains_full_row m j

/-- The distinguished row-fiber of the exceptional set is full. -/
theorem rowBad_zero_fiber_card (m : ℕ) :
    ((rowBad m).filter (fun x => x.1 = rowZero m)).card = m + 1 := by
  have hfilter : (rowBad m).filter (fun x => x.1 = rowZero m) = rowBad m := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, (mem_rowBad_iff_first_eq_rowZero m x).mp hx⟩
  rw [hfilter, rowBad_card]

/-- The one-row obstruction has Cartesian density exactly `1/(m+1)` in cardinal form.

Equivalently: a global discrepancy/error budget allowing `(m+1)` bad Cartesian pairs cannot rule out
one completely uncontrolled row of length `(m+1)`.  Uniform row control needs a strictly smaller
budget than one row. -/
theorem rowBad_card_mul_eq_grid_card (m : ℕ) :
    (rowBad m).card * (m + 1) = Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
  rw [rowBad_card]
  simp [Fintype.card_prod]

/-- Honest scope marker: this is only a Cartesian-to-row selection barrier. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms rowBad_card
#print axioms rowBad_contains_full_row
#print axioms mem_rowBad_iff_first_eq_rowZero
#print axioms rowBad_zero_fiber_card
#print axioms rowBad_card_mul_eq_grid_card
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G249CartesianRowSelectionBarrier
