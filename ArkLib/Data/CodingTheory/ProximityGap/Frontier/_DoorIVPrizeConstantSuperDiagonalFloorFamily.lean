/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeShawTetrachotomySynthesis

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lane-3: the FAMILY prize-constant lower bound `c₀ ≤ K` from a uniform super-diagonal floor (#444)

`_DoorIVPrizeShawTetrachotomySynthesis` proved the *pointwise* prize-constant lower bound:
`superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor` — if the proven super-diagonal
period floor `c₀·√n ≤ M` (`c₀ = (5/4)^{1/4} ≈ 1.0574 > 1`) holds and `M ≤ K·√n`, then necessarily
`c₀ ≤ K`.  So a single floor-normalized prize certificate cannot have a constant below `c₀`, strictly
above the bare Plancherel `1`.

But the prize is an `∀`-family statement: it demands a SINGLE absolute constant `K` valid across the
whole admissible thin family `{(nᵢ, Mᵢ)}`.  Only the pointwise constant lower bound existed; there was
no statement that a *uniform* super-diagonal floor `c₀·√nᵢ ≤ Mᵢ` over the family forces that uniform
prize constant `K` itself to satisfy `c₀ ≤ K`.

This module closes that one rung — the family companion.  It chains the **already-proven** pointwise
prize-constant lower bound over an `ι`-indexed family, giving:

* `superDiagonalFloorConst_le_familyPrizeFloorConstant` — any uniform floor-scale prize constant `K`
  valid for a family with a uniform super-diagonal floor satisfies `c₀ ≤ K`;
* `not_familyPrizeFloorConstant_lt_superDiagonal` — contrapositive: no uniform floor-scale prize
  constant below `c₀` can hold over such a family.

WHY IT MATTERS: this is the family-level lower bound on the *achievable prize constant itself*.  The
$1M prize asks for an absolute `C` with `Mᵢ ≤ C·√nᵢ` uniformly; this lemma certifies that any such `C`
is provably `≥ c₀ = (5/4)^{1/4} > 1` (given the unconditional super-diagonal floor over the family) —
the prize constant is bounded away from the bare Plancherel `1` from below, uniformly.

## Scope (honesty)

Lane-3 constraint lemma ONLY.  It is a pure pointwise lift of the established single-instance
prize-constant lower bound to an `ι`-indexed family.  It proves NO prize inequality (it bounds the
prize constant from BELOW, the easy direction — the open problem is the UPPER bound `C = O(1)`), gives
NO anti-concentration / cancellation estimate, and asserts the super-diagonal floor holds at NO
instance (it is a hypothesis, the proven `worstPeriod_ge_const_sqrt` conclusion-shape).  CORE remains
exactly as open as before.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis

open ArkLib.ProximityGap.Frontier

variable {ι : Type*} {M n : ι → ℝ} {K : ℝ}

/-- **Family prize-constant lower bound from a uniform super-diagonal floor.**  If every member of an
admissible thin family satisfies the proven super-diagonal period floor `c₀·√nᵢ ≤ Mᵢ`
(`c₀ = (5/4)^{1/4}`), and a single uniform floor-scale prize constant `K` bounds the whole family
(`Mᵢ ≤ K·√nᵢ` for all `i`), then necessarily `c₀ ≤ K`.  Family companion of
`superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor`.

The family must be NONEMPTY (`[Nonempty ι]`): with no instances there is no constraint on `K`. -/
theorem superDiagonalFloorConst_le_familyPrizeFloorConstant [Nonempty ι]
    (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hbound : ∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact superDiagonalFloorConst_le_prizeFloorConstant_of_superDiagonal_floor
    (hn i) (hfloor i) (hbound i)

/-- **No uniform floor-scale prize constant below `c₀`.**  Contrapositive of the family lower bound:
over a nonempty admissible family with a uniform super-diagonal floor, no uniform floor-scale prize
constant `K < c₀ = (5/4)^{1/4}` can hold.  So a putative prize certificate with a constant below the
super-diagonal floor is impossible for the whole family. -/
theorem not_familyPrizeFloorConstant_lt_superDiagonal [Nonempty ι]
    (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hlt : K < ShawValueCapstone.superDiagonalFloorConst) :
    ¬ (∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) := by
  intro hbound
  exact absurd (superDiagonalFloorConst_le_familyPrizeFloorConstant hn hfloor hbound)
    (not_le.2 hlt)

/-- **Family prize-constant lower bound, packaged with the strict-above-one fact.**  Over a nonempty
admissible family with a uniform super-diagonal floor: any uniform floor-scale prize constant `K`
satisfies `c₀ ≤ K`, and `c₀ > 1`, so `K > 1` strictly.  One citable family statement that the
achievable prize constant is bounded below by the super-diagonal floor, strictly above the bare
Plancherel `1`. -/
theorem familyPrizeFloorConstant_ge_superDiagonal_gt_one [Nonempty ι]
    (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hbound : ∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) :
    ShawValueCapstone.superDiagonalFloorConst ≤ K
      ∧ (1 : ℝ) < ShawValueCapstone.superDiagonalFloorConst
      ∧ (1 : ℝ) < K :=
  ⟨superDiagonalFloorConst_le_familyPrizeFloorConstant hn hfloor hbound,
    ShawValueCapstone.superDiagonalFloorConst_gt_one,
    lt_of_lt_of_le ShawValueCapstone.superDiagonalFloorConst_gt_one
      (superDiagonalFloorConst_le_familyPrizeFloorConstant hn hfloor hbound)⟩

/-- **No uniform unit prize constant.**  Over a nonempty admissible family with a uniform
super-diagonal floor, a floor-scale prize constant at or below the bare Plancherel value `1` cannot
hold.  This is the `K ≤ 1` consumer of the family lower bound `c₀ ≤ K` and the strict fact `1 < c₀`. -/
theorem not_familyPrizeFloorConstant_le_one [Nonempty ι]
    (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hK : K ≤ 1) :
    ¬ (∀ i, M i ≤ K * NoFifthDoorTetrachotomy.prizeScale (n i)) := by
  intro hbound
  have hle : ShawValueCapstone.superDiagonalFloorConst ≤ K :=
    superDiagonalFloorConst_le_familyPrizeFloorConstant hn hfloor hbound
  exact not_lt_of_ge (le_trans hle hK) ShawValueCapstone.superDiagonalFloorConst_gt_one

/-- **No uniform Plancherel-unit prize certificate.**  The concrete `K = 1` specialization of the
unit-baseline no-go: under a uniform super-diagonal floor, the family cannot be bounded by the bare
floor-scale `√nᵢ` at every instance.  Any valid uniform prize constant must be strictly above `1`. -/
theorem not_familyPrizeFloorConstant_one [Nonempty ι]
    (hn : ∀ i, 0 < n i)
    (hfloor : ∀ i, ShawValueCapstone.superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ¬ (∀ i, M i ≤ NoFifthDoorTetrachotomy.prizeScale (n i)) := by
  simpa using (not_familyPrizeFloorConstant_le_one (M := M) (n := n) (K := (1 : ℝ))
    hn hfloor le_rfl)

end ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis
