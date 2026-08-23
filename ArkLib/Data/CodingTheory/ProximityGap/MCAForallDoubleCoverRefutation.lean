/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingRefutation

/-!
# The `MCAForallDoubleCover` predicate is false in general (regression guard, #140 / #169 / #171)

`ArkLib/ResidualAxioms.lean` names the open ABF26-T4.21 surface
`mcaForallDoubleCover_residual : … MCAForallDoubleCover C δ`. It was at one point a laundering
`axiom` (asserting it for *all* codes); it is now correctly a non-asserting `def : Prop`. This
file records *why* it must stay that way: `MCAForallDoubleCover` is **not** universally true, so
it can never honestly be re-promoted to an `axiom`/`theorem`.

`LineDecodingRefutation.lean` already exhibits a concrete realizable bad event
(`mcaEvent_ubad_zero`, with `epsMCA_Czero_pos` and the black-box refutation
`lineDecodable_imp_epsMCA_le_false`). We **reuse that witness** — no new construction — and combine
it with `MCAForallDoubleCover.not_mcaEvent` (`MCAForallDoubleCover C δ → ∀ u γ, ¬ mcaEvent …`) to
refute the `MCAForallDoubleCover` predicate directly:

* `not_mcaForallDoubleCover_Czero` — `¬ MCAForallDoubleCover (Czero) 0`.
* `exists_not_mcaForallDoubleCover` — hence `∃ C δ, ¬ MCAForallDoubleCover C δ`; the universal
  reading of `mcaForallDoubleCover_residual` is a false proposition.

A refutation/guard artifact, not a closure of any open problem. Tracking: Issues #140, #169, #171.
-/

open CodingTheory.LineDecodingRefutation
open scoped NNReal

namespace ProximityGap

/-- **`MCAForallDoubleCover` fails for the zero code at radius `0`.** If it held, then by
`MCAForallDoubleCover.not_mcaEvent` no MCA bad event could occur — but `mcaEvent_ubad_zero`
exhibits one for the `ubad` stack at `γ = 0`. -/
theorem not_mcaForallDoubleCover_Czero :
    ¬ MCAForallDoubleCover (F := F) (A := A) (Czero : Set (ι → A)) 0 := fun hcov =>
  MCAForallDoubleCover.not_mcaEvent (F := F) (A := A) (Czero : Set (ι → A)) 0 hcov
    ubad 0 mcaEvent_ubad_zero

/-- **The universal `mcaForallDoubleCover_residual` reading is a false proposition.** There is a
concrete code/radius at which `MCAForallDoubleCover` fails, so the residual must remain an open,
non-asserting `def : Prop` (it cannot be honestly re-laundered into an `axiom`/theorem). -/
theorem exists_not_mcaForallDoubleCover :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F)
      (A : Type) (_ : Fintype A) (_ : DecidableEq A) (_ : AddCommGroup A) (_ : Module F A)
      (C : Set (ι → A)) (δ : ℝ≥0), ¬ MCAForallDoubleCover (F := F) (A := A) C δ :=
  ⟨ι, inferInstance, inferInstance, inferInstance,
    F, inferInstance, inferInstance, inferInstance,
    A, inferInstance, inferInstance, inferInstance, inferInstance,
    (Czero : Set (ι → A)), 0, not_mcaForallDoubleCover_Czero⟩

end ProximityGap

#print axioms ProximityGap.not_mcaForallDoubleCover_Czero
#print axioms ProximityGap.exists_not_mcaForallDoubleCover
