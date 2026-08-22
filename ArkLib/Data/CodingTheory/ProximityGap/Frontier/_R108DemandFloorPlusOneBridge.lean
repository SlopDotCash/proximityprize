/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DemandFloorReduction

/-!
# Demand-side floor bridge with the zero-orbit `+1`

`DemandFloorReduction.demand_floor_of_orbit_bound` clears the main term

`2*m*OP ≤ 2^r * C(m,r)`

from the orbit-count hypothesis `OP ≤ C(m,r-1)`.  The documented orbit identity for the actual
bad-scalar count has one additional possible zero orbit:

`#bad ≤ 2*m*OP + 1`.

This file proves that the same orbit-count hypothesis clears that `+1` in the prize range
`4 ≤ r`, `2*r ≤ m`.  Thus the demand-side consumer can use the honest identity shape directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R108DemandFloorPlusOneBridge

open Nat
open ArkLib.ProximityGap.DemandFloorReduction

/-- Strengthened clearance: in the demand-floor range, the orbit budget has at least one unit of
slack after the possible zero orbit is included. -/
theorem demand_floor_plus_one_of_orbit_bound (m r OP : ℕ)
    (hr : 4 ≤ r) (hm : 2 * r ≤ m)
    (hOP : OP ≤ m.choose (r - 1)) :
    2 * m * OP + 1 ≤ 2 ^ r * m.choose r := by
  have hrpos : 0 < r := by omega
  have hr1 : 1 ≤ r := by omega
  have hmpos : 0 < m := by omega
  have hOPmain : 2 * m * OP ≤ 2 ^ r * m.choose r :=
    demand_floor_of_orbit_bound m r OP hr hm hOP
  by_cases hprev : m.choose (r - 1) = 0
  · have hOP0 : OP = 0 := by omega
    subst hOP0
    have hrle : r ≤ m := by omega
    have hchoose_pos : 0 < m.choose r := Nat.choose_pos hrle
    have hbudget_pos : 0 < 2 ^ r * m.choose r :=
      Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) r) hchoose_pos
    omega
  · have hprev_pos : 0 < m.choose (r - 1) := Nat.pos_of_ne_zero hprev
    have hch : m.choose r * r = m.choose (r - 1) * (m - r + 1) := by
      have h := Nat.choose_succ_right_eq m (r - 1)
      rw [Nat.sub_add_cancel hr1] at h
      rw [h]; congr 1; omega
    have hprev_large : r ≤ m.choose (r - 1) := by
      have htop : r ≤ m := by omega
      have hmono : r.choose (r - 1) ≤ m.choose (r - 1) :=
        Nat.choose_le_choose (r - 1) htop
      have hself : r.choose (r - 1) = r := by
        have h := Nat.choose_succ_self_right (r - 1)
        rw [Nat.sub_add_cancel hr1] at h
        simpa [Nat.sub_add_cancel hr1] using h
      omega
    have hcl := clearance m r hr hm
    -- The scalar clearance has a positive margin, not merely a weak inequality.
    have hcl_plus : 2 * m * r + r ≤ 2 ^ r * (m - r + 1) := by
      have hmr : m ≤ 2 * (m - r + 1) := by omega
      have h4r : 4 * r ≤ 2 ^ r := four_mul_le_two_pow r hr
      have hbase : 2 * m * r ≤ 2 ^ r * (m - r + 1) := hcl
      -- At the left endpoint `m = 2r`, the gap is already positive; monotonicity in `m`
      -- is enough for the whole range.
      have hgap : 2 * m * r + r ≤ (4 * r) * (m - r + 1) := by
        obtain ⟨e, he⟩ : ∃ e, m = 2 * r + e := ⟨m - 2 * r, by omega⟩
        subst he
        have hsub : 2 * r + e - r + 1 = r + e + 1 := by omega
        rw [hsub]
        nlinarith [hr, Nat.zero_le e]
      exact le_trans hgap (Nat.mul_le_mul_right (m - r + 1) h4r)
    -- Multiply the positive scalar margin by `C(m,r-1)`; then absorb `r`.
    have hmul :
        (2 * m * m.choose (r - 1) + 1) * r
          ≤ (2 ^ r * m.choose r) * r := by
      calc (2 * m * m.choose (r - 1) + 1) * r
          ≤ (2 * m * m.choose (r - 1) + m.choose (r - 1)) * r := by
              gcongr
              omega
        _ = (2 * m * r + r) * m.choose (r - 1) := by ring
        _ ≤ (2 ^ r * (m - r + 1)) * m.choose (r - 1) := by gcongr
        _ = 2 ^ r * (m.choose (r - 1) * (m - r + 1)) := by ring
        _ = 2 ^ r * (m.choose r * r) := by rw [← hch]
        _ = (2 ^ r * m.choose r) * r := by ring
    have hplus_choose : 2 * m * m.choose (r - 1) + 1 ≤ 2 ^ r * m.choose r :=
      Nat.le_of_mul_le_mul_right hmul hrpos
    have hleft : 2 * m * OP + 1 ≤ 2 * m * m.choose (r - 1) + 1 := by
      gcongr
    exact le_trans hleft hplus_choose

/-- Consumer form: if an actual bad-scalar count is bounded by the orbit identity
`#bad ≤ 2*m*OP + 1`, then the orbit conjecture gives the full demand-side budget. -/
theorem demand_floor_count_of_orbit_bound_plus_one (m r OP bad : ℕ)
    (hr : 4 ≤ r) (hm : 2 * r ≤ m)
    (hOP : OP ≤ m.choose (r - 1))
    (hbad : bad ≤ 2 * m * OP + 1) :
    bad ≤ 2 ^ r * m.choose r :=
  le_trans hbad (demand_floor_plus_one_of_orbit_bound m r OP hr hm hOP)

end ArkLib.ProximityGap.Frontier.R108DemandFloorPlusOneBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R108DemandFloorPlusOneBridge.demand_floor_plus_one_of_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R108DemandFloorPlusOneBridge.demand_floor_count_of_orbit_bound_plus_one
