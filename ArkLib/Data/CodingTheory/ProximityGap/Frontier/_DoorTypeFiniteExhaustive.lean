/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# DoorType finiteness / exhaustiveness capstone — the literal "no fifth door" (#444, Lane 3)

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy.lean`) proves the *scale* exclusion:
classical doors overshoot BGK, so only door (iv) certifies a prize-scale bound.  The
`DoorType.isClassical_iff_ne_newEvaluation` complement is there.  But the **combinatorial backbone**
the name "tetrachotomy / no fifth door" asserts — that `DoorType` has **exactly four** inhabitants,
partitioned into **exactly three** classical (dead) doors and **exactly one** live door
(`newEvaluation`) — was never stated as a kernel-checked finiteness fact.  `DoorType` derives only
`DecidableEq, Repr`, not `Fintype`.

This module closes that gap with real, axiom-clean `Fintype`/cardinality statements:

* `Fintype DoorType` instance + `card_doorType : Fintype.card DoorType = 4` — there are exactly four
  doors, no fifth constructor (kernel-checked, not prose);
* `univ_doorType` — the explicit enumeration `{moment, completion, extremeValue, newEvaluation}`;
* `card_classical_doors = 3` and `card_nonClassical_doors = 1` — the 3-dead / 1-live split as
  cardinalities, with `newEvaluation` the unique non-classical door;
* `existsUnique_nonClassicalDoor` — the unique-live-door fact as an `∃!` eliminator;
* `classical_add_live_eq_total` — `3 + 1 = 4` as a partition fact: the classical doors plus the single
  live door exhaust all four.

**Scope / honesty.** This is the finite-combinatorics backbone of the tetrachotomy's NAME — it makes
"four doors, three dead, one live, no fifth" a kernel-checked statement.  It is purely about the
`DoorType` enumeration; it makes **no** analytic / scale / CORE / cancellation / anti-concentration /
capacity claim, and does **not** assert any door is achievable or dead (the *scale* content lives in
`_NoFifthDoorTetrachotomy`).  It only certifies the shape of the case-split is exactly four-way.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

/-- `DoorType.isClassical` is decidable: it is `True` on the three classical doors and `False` on
`newEvaluation`, so the classical/live split is computable (needed for the `Finset.filter`s below). -/
instance moduleInstance_DoorTypeFiniteExhaustive_1 : DecidablePred (fun d : DoorType => d.isClassical) := fun d => by
  cases d <;> unfold DoorType.isClassical <;> infer_instance

/-- `DoorType` is a finite type: the four-door enumeration is total.  Derived from the explicit
universe list, this is the kernel witness that there is no fifth constructor. -/
instance moduleInstance_DoorTypeFiniteExhaustive_2 : Fintype DoorType where
  elems := {DoorType.moment, DoorType.completion, DoorType.extremeValue, DoorType.newEvaluation}
  complete := by intro d; cases d <;> decide

/-- **Exactly four doors.**  `Fintype.card DoorType = 4`: the tetrachotomy is genuinely a
*tetra*-chotomy — four doors, kernel-checked, no fifth. -/
theorem card_doorType : Fintype.card DoorType = 4 := by decide

/-- **The explicit door enumeration.**  `Finset.univ` over `DoorType` is exactly the four named
doors — the literal exhaustive list backing every four-way case split. -/
theorem univ_doorType :
    (Finset.univ : Finset DoorType) =
      {DoorType.moment, DoorType.completion, DoorType.extremeValue, DoorType.newEvaluation} := by
  decide

/-- **Exactly one non-classical door.**  Filtering `univ` by `¬ isClassical` leaves precisely
`{newEvaluation}`: door (iv) is the unique live door. -/
theorem filter_not_classical_eq :
    (Finset.univ.filter (fun d : DoorType => ¬ d.isClassical)) = {DoorType.newEvaluation} := by
  decide

/-- **Exactly three classical doors.**  The classical (proven-dead) doors are precisely
`{moment, completion, extremeValue}` — three of them. -/
theorem filter_classical_eq :
    (Finset.univ.filter (fun d : DoorType => d.isClassical)) =
      {DoorType.moment, DoorType.completion, DoorType.extremeValue} := by
  decide

/-- **Three classical doors (cardinality).**  Exactly three of the four doors are classical/dead. -/
theorem card_classical_doors :
    (Finset.univ.filter (fun d : DoorType => d.isClassical)).card = 3 := by decide

/-- **One live door (cardinality).**  Exactly one of the four doors is non-classical: door (iv). -/
theorem card_nonClassical_doors :
    (Finset.univ.filter (fun d : DoorType => ¬ d.isClassical)).card = 1 := by decide

/-- **The 3-dead / 1-live partition exhausts all four doors.**  `card classical + card non-classical
= card DoorType = 4`: the three dead doors and the single live door (iv) partition the entire
tetrachotomy, with nothing left over — the kernel-checked "no fifth door, three dead plus one live." -/
theorem classical_add_live_eq_total :
    (Finset.univ.filter (fun d : DoorType => d.isClassical)).card
      + (Finset.univ.filter (fun d : DoorType => ¬ d.isClassical)).card
    = Fintype.card DoorType := by
  rw [card_classical_doors, card_nonClassical_doors, card_doorType]

/-- **`newEvaluation` is the unique live door (membership form).**  A door is non-classical iff it is
`newEvaluation`, packaged against the singleton filter — the live door is unique and named. -/
theorem mem_nonClassical_iff_newEvaluation (d : DoorType) :
    d ∈ Finset.univ.filter (fun d : DoorType => ¬ d.isClassical) ↔ d = DoorType.newEvaluation := by
  rw [filter_not_classical_eq, Finset.mem_singleton]

/-- **The unique-live-door eliminator.**  There exists exactly one non-classical door, namely
door (iv) `newEvaluation`.  This is the `∃!` form of the no-fifth-door combinatorial backbone,
convenient for consumers that want uniqueness rather than a filtered-cardinality statement. -/
theorem existsUnique_nonClassicalDoor : ∃! d : DoorType, ¬ d.isClassical := by
  refine ⟨DoorType.newEvaluation, ?_, ?_⟩
  · decide
  · intro d hd
    exact (DoorType.not_classical_iff_eq_newEvaluation d).mp hd

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

#print axioms ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.existsUnique_nonClassicalDoor
