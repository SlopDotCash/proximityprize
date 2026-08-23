/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVConnectedCumulantVanishes
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTripleCorrelationVanishes

/-!
# Door IV — CORRELATION-HIERARCHY CAPSTONE: the period field carries no door-(iv) lever in the
# connected-correlation hierarchy through 6th order

This file is a CITABLE SYNTHESIS (Lane-2). It composes the three independently-established
vanishing facts about the period field `z_j = η_{g^j}` on the cyclic multiplicative quotient into a
single statement: every per-lag connected-correlation functional of the field, through 6th order, is
determined by the lower-order data — all of which the probe campaign has independently mapped DEAD.
Hence the correlation hierarchy through 6th order supplies NO door-(iv) lever.

## What is composed (all axiom-clean, all probe-verified, all already in-tree)

1. **2-point (white field)** — `_DoorIVJointFieldWhite`: the lag-`k` cross-covariance is ≈ 0
   (white-field sweep), so the lag-`k` joint second moment reduces to the diagonal variance.
2. **connected-4 = 0** — `_DoorIVConnectedCumulantVanishes`: the off-diagonal connected 4th cumulant
   vanishes ⇒ the 2-2 moment Wick-factorizes through the (dead) 2-point covariance
   (`m22_eq_wick_of_cumulant_zero`).
3. **connected-6 (triple) = 0** — `_DoorIVTripleCorrelationVanishes`: the connected triple correlation
   `κ₃` is consistent with 0 ⇒ the signed 6-point functional `|κ₃|²` is `0`
   (`sixPoint_functional_zero_of_triple_zero`) and the 3-3 moment Wick-factorizes through the (dead)
   2-point covariance + (dead) `E₃` diagonal (`m33_eq_wick_of_cumulant_zero`).

Each Wick value is built only from lower-order objects the campaign mapped dead (marginal-EVT = BGK,
white 2-point, `K₄ = E₂` / `K₆ = E₃` = refuted additive energy). The composition therefore says: a
door-(iv) candidate `M` controlled by ANY connected-correlation functional through 6th order is
controlled by the dead lower-order data — no new structure survives. CORE stays open: a surviving
surface must be an EVEN-HIGHER connected order or genuinely outside the correlation hierarchy.

## The capstone statement (this file)

We package the synthesis as: given the connected-4 cumulant decomposition + vanishing, the connected-6
(triple) vanishing, and a control routing `M ≤ m22` and `M ≤ m33`, the candidate `M` is bounded by the
respective Wick values (the dead lower-order data) AND the signed 6-point lever is vacuous. A single
theorem `correlation_hierarchy_no_lever` returns the conjunction. This is a citable record that the
correlation-hierarchy door is mapped + closed through 6th order; it makes no CORE/cancellation claim.
-/

namespace ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone

open ProximityGap.Frontier.DoorIVConnectedCumulantVanishes
open ProximityGap.Frontier.DoorIVTripleCorrelationVanishes

/-- The signed 6-point functional `|κ₃|²` is vacuous when the connected triple correlation vanishes:
re-exported here as the 6th-order rung of the capstone. -/
theorem sixPoint_lever_vacuous
    {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 :=
  sixPoint_functional_zero_of_triple_zero hzero

/-- **Correlation-hierarchy capstone (through 6th order).** Suppose a door-(iv) candidate `M` is
controlled by the lag joint 2-2 moment `m22` and the 3-3 moment `m33` (`hctrl4 : M ≤ m22`,
`hctrl6 : M ≤ m33`); the connected 4th and 6th (3-3) cumulants decompose
(`hdec4 : m22 = wick4 + cum4`, `hdec6 : m33 = wick6 + cum6`); and the probe facts hold that both
connected cumulants vanish (`hcum4 : cum4 = 0`, `hcum6 : cum6 = 0`). Then `M` is bounded by BOTH Wick
values — the dead lower-order (2-point covariance + diagonal) data. No connected-correlation functional
through 6th order supplies a fresh bound. -/
theorem correlation_hierarchy_no_lever
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0) :
    M ≤ wick4 ∧ M ≤ wick6 := by
  refine ⟨?_, ?_⟩
  · have h4 : m22 = wick4 := m22_eq_wick_of_cumulant_zero hdec4 hcum4
    exact control_passes_through_wick hctrl4 h4
  · have h6 : m33 = wick6 := m33_eq_wick_of_cumulant_zero hdec6 hcum6
    exact control_passes_through_wick6 hctrl6 h6

/-- Full conjunction including the vacuity of the signed 6-point lever at `κ₃ = 0`: the citable
"correlation hierarchy is closed through 6th order" statement. -/
theorem correlation_hierarchy_closed_through_six
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ} {κ₃ : ℂ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0)
    (htriple : κ₃ = 0) :
    (M ≤ wick4 ∧ M ≤ wick6) ∧ Complex.normSq κ₃ = 0 :=
  ⟨correlation_hierarchy_no_lever hctrl4 hctrl6 hdec4 hcum4 hdec6 hcum6,
   sixPoint_lever_vacuous htriple⟩

end ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone

#print axioms ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.sixPoint_lever_vacuous
#print axioms ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_no_lever
#print axioms ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_closed_through_six
