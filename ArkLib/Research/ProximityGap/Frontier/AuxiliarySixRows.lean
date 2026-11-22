/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotRow
import ArkLib.Research.ProximityGap.Frontier.AuxiliaryRatioSlotFacts
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceNormalize

/-! # All six auxiliary order-128 rows obey the twelve-unit penalty bound -/

namespace ProximityGap.AuxiliarySixRows
open AuxiliaryRatioSlotData AuxiliaryRatioSlotFacts TwoErrorSlice

/-- The unconditional row bound for each archived separation. -/
theorem row {d : ℕ} (hd : Row d) : RowPenaltyBound domain 0 (site d hd) :=
  AuxiliaryRatioSlotRow.row_of_facts d (data d) domain (site d hd) rfl (ratio_eq hd)
    (key_lt hd) (key_injective hd) (pair_injective hd) (pair_tagged hd)
    (charge_injective hd) (charge_tag_lt hd)

/-- Finite-index form of the six row bounds for transfer to other prime fields. -/
theorem six (d : Fin 128) (hd : StandardRow d) : RowPenaltyBound domain 0 d := by
  have valid : Row d.val := by
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact row valid

end ProximityGap.AuxiliarySixRows
#print axioms ProximityGap.AuxiliarySixRows.six
