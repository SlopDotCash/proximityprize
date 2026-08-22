/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import Mathlib.Order.Interval.Set.Basic

/-!
# The door-(iv) target corridor as a genuine `Set.Icc` (#444, Lane 2 capstone packaging)

`_NoFifthDoorTetrachotomy.lean` pins the worst-frequency sup `M` to the corridor
`[prizeScale n, bgkScale n L] = [√n, √(n·L)]` via `mem_doorIV_corridor`, but that theorem returns a
bare conjunction `prizeScale n ≤ M ∧ M ≤ bgkScale n L`.  This module packages the corridor as a real
`Set.Icc`, so downstream statements can use the order-theoretic interface (`Set.mem_Icc`,
`Set.Nonempty`, `Set.Icc_subset_Icc`, monotonicity) instead of re-deriving the two-sided bound.

Contents (all axiom-clean, pure order/`Real.sqrt` bookkeeping — no analytic/CORE claim):

* `doorIVCorridor` — the interval `Set.Icc (prizeScale n) (bgkScale n L)` as a named set;
* `mem_doorIVCorridor_iff` — `M ∈ doorIVCorridor ↔ √n ≤ M ∧ M ≤ √(n·L)` (the `Set.Icc` bridge);
* `mem_doorIVCorridor_of_bounds` / endpoint membership / endpoint exclusion — membership in/out;
* `doorIVCorridor_nonempty` — the corridor is nonempty in the prize regime `L > 1`;
* endpoint strictness from membership plus inequality — corridor points away from either endpoint;
* `doorIVCorridor_subset_of_le` — corridor monotonicity in the thinness index `L`.

**Scope / honesty.** Pure reduction/packaging of the already-proven corridor endpoints into the
`Set.Icc` interface.  No CORE / cancellation / completion / moment / anti-concentration / capacity
claim; the corridor *width* `√L` is the door-(iv) obligation and is NOT shaved here.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy Set

/-- The door-(iv) target corridor as a `Set.Icc`: the closed interval
`[prizeScale n, bgkScale n L] = [√n, √(n·L)]` in which the worst-frequency sup `M` lives. -/
noncomputable def doorIVCorridor (n L : ℝ) : Set ℝ :=
  Set.Icc (prizeScale n) (bgkScale n L)

/-- **The `Set.Icc` bridge.**  `M` is in the door-(iv) corridor exactly when it satisfies the
Plancherel floor and the BGK ceiling: `√n ≤ M ≤ √(n·L)`. -/
theorem mem_doorIVCorridor_iff {n L M : ℝ} :
    M ∈ doorIVCorridor n L ↔ prizeScale n ≤ M ∧ M ≤ bgkScale n L := by
  unfold doorIVCorridor
  exact Set.mem_Icc

/-- Build corridor membership from the two proven bounds (the `Set.Icc` form of
`mem_doorIV_corridor`). -/
theorem mem_doorIVCorridor_of_bounds {n L M : ℝ}
    (hfloor : prizeScale n ≤ M) (hceil : M ≤ bgkScale n L) :
    M ∈ doorIVCorridor n L :=
  mem_doorIVCorridor_iff.mpr ⟨hfloor, hceil⟩

/-- The prize floor itself sits in the corridor in the prize regime `L > 1` (the lower endpoint is the
prize target). -/
theorem prizeScale_mem_doorIVCorridor {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n ∈ doorIVCorridor n L :=
  mem_doorIVCorridor_of_bounds le_rfl (le_of_lt (prizeScale_lt_bgkScale hn hL))

/-- The BGK ceiling itself sits in the corridor in the prize regime `L > 1` (the upper endpoint is
what doors (i)-(iii) can already certify, before the missing door-(iv) shaving). -/
theorem bgkScale_mem_doorIVCorridor {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    bgkScale n L ∈ doorIVCorridor n L :=
  mem_doorIVCorridor_of_bounds (le_of_lt (prizeScale_lt_bgkScale hn hL)) le_rfl

/-- **Nothing below the Plancherel floor is in the corridor.**  A value strictly under `√n` cannot be
the worst-frequency sup: the prize floor is a hard lower endpoint. -/
theorem not_mem_doorIVCorridor_of_lt_prizeScale {n L M : ℝ} (hM : M < prizeScale n) :
    M ∉ doorIVCorridor n L := by
  rw [mem_doorIVCorridor_iff]
  rintro ⟨hfloor, _⟩
  exact absurd hfloor (not_le.mpr hM)

/-- **Nothing above the BGK ceiling is in the corridor.**  A value strictly over `√(n·L)` has already
left the door-(iv) target corridor; the ceiling endpoint is just as hard as the prize floor. -/
theorem not_mem_doorIVCorridor_of_bgkScale_lt {n L M : ℝ} (hM : bgkScale n L < M) :
    M ∉ doorIVCorridor n L := by
  rw [mem_doorIVCorridor_iff]
  rintro ⟨_, hceil⟩
  exact absurd hceil (not_le.mpr hM)

/-- **The corridor is nonempty** in the prize regime `L > 1`: its endpoints satisfy
`√n < √(n·L)`, so the closed interval is a genuine (positive-width) interval, not empty. -/
theorem doorIVCorridor_nonempty {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    (doorIVCorridor n L).Nonempty :=
  ⟨prizeScale n, prizeScale_mem_doorIVCorridor hn hL⟩

/-- A corridor point that is not the floor is strictly above it (`√n < M`): such an `M` certifies the
door-(iv) gap is partially unpaid. -/
theorem prizeScale_lt_of_mem_doorIVCorridor_of_ne {n L M : ℝ}
    (hmem : M ∈ doorIVCorridor n L) (hne : M ≠ prizeScale n) :
    prizeScale n < M :=
  lt_of_le_of_ne ((mem_doorIVCorridor_iff.mp hmem).1) (Ne.symm hne)

/-- A corridor point that is not the BGK ceiling is strictly below it (`M < √(n·L)`).  This is the
upper-endpoint analogue of `prizeScale_lt_of_mem_doorIVCorridor_of_ne`: any non-ceiling point has
already shaved at least some of the classical BGK slack, without claiming a uniform saving. -/
theorem lt_bgkScale_of_mem_doorIVCorridor_of_ne {n L M : ℝ}
    (hmem : M ∈ doorIVCorridor n L) (hne : M ≠ bgkScale n L) :
    M < bgkScale n L :=
  lt_of_le_of_ne ((mem_doorIVCorridor_iff.mp hmem).2) hne

/-- At `L = 1` the door-(iv) corridor collapses to the singleton floor `{√n}`.  Thus every
positive-width corridor statement genuinely uses the thinness slack `L > 1`; at the endpoint there is
no room between the Plancherel floor and the BGK ceiling. -/
theorem doorIVCorridor_one_eq_singleton (n : ℝ) :
    doorIVCorridor n 1 = {prizeScale n} := by
  unfold doorIVCorridor bgkScale prizeScale
  simp

/-- Endpoint-collapse membership form: when `L = 1`, being in the door-(iv) corridor is exactly being
at the Plancherel floor.  This is the no-slack boundary case of the corridor interface. -/
theorem mem_doorIVCorridor_one_iff {n M : ℝ} :
    M ∈ doorIVCorridor n 1 ↔ M = prizeScale n := by
  rw [doorIVCorridor_one_eq_singleton]
  simp

/-- **Corridor monotonicity in the thinness index.**  A larger thinness index `L₁ ≤ L₂` (with `0 ≤ n`)
yields a wider BGK ceiling, hence a larger corridor: `doorIVCorridor n L₁ ⊆ doorIVCorridor n L₂`.
The floor `√n` is `L`-independent; only the ceiling `√(n·L)` grows. -/
theorem doorIVCorridor_subset_of_le {n L₁ L₂ : ℝ} (hn : 0 ≤ n) (hL : L₁ ≤ L₂) :
    doorIVCorridor n L₁ ⊆ doorIVCorridor n L₂ := by
  unfold doorIVCorridor
  apply Set.Icc_subset_Icc le_rfl
  unfold bgkScale
  exact Real.sqrt_le_sqrt (by nlinarith [hn])

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale_mem_doorIVCorridor
#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.not_mem_doorIVCorridor_of_bgkScale_lt
#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.lt_bgkScale_of_mem_doorIVCorridor_of_ne
#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIVCorridor_one_eq_singleton
#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.mem_doorIVCorridor_one_iff
