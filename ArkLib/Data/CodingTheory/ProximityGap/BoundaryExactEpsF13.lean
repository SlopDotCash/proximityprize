/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness

set_option maxHeartbeats 2000000

/-!
# An exact boundary-band MCA value over `F_13` (#389)

A second concrete instance of the boundary-band exactness law `rs_boundary_epsMCA_eq`
(`epsMCA = n/q`), companion to `BoundaryExactEpsF19` (`epsMCA = 9/19`).  For the smooth Reed–Solomon
code `RS[F_13, μ_12, 8]` (`μ_12 = ⟨2⟩`, `2` a primitive 12th root of unity, `2^12 = 1`) at the
boundary radius `δ = 1/6`:

> **`epsMCA_boundary_F13_n12`** — `epsMCA(RS[F_13, μ_12, 8], 1/6) = 12/13`.

Here `δ·n = 12/6 = 2 ∈ [2, 3)`, `3 ∣ 12`, `6 < 12`, `k = 12 − 4 = 8` — all hypotheses of the generic
sandwich.  Together with the `q=19` instance this exhibits the `n/q` law across two distinct fields
and band parameters (`(n,q) = (9,19)` and `(12,13)`); the value is the MCA *equality*, not a witness
count.  Axiom-clean.
-/

open scoped NNReal ENNReal
open ProximityGap Code ProximityGap.CensusLowerBound ProximityGap.SmoothLadderInstance
  ProximityGap.MCAThresholdLedger ProximityGap.BoundarySupExactness

namespace ProximityGap.BoundaryExactEpsF13

instance primeFact_BoundaryExactEpsF13_1 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Exact boundary MCA value over `F_13`.**  For `RS[F_13, μ_12, 8]` (`μ_12 = ⟨2⟩`,
`orderOf 2 = 12`) at the boundary radius `δ = 1/6` (so `δ·n = 2 ∈ [2, 3)`), the boundary-band law
gives `epsMCA = n/q = 12/13`. -/
theorem epsMCA_boundary_F13_n12 :
    epsMCA (F := ZMod 13) (A := ZMod 13)
      (evalCode (smoothDom (2 : ZMod 13) 12) 8 : Set (Fin 12 → ZMod 13)) (1 / 6 : ℝ≥0)
      = (12 : ℝ≥0∞) / (13 : ℝ≥0∞) := by
  have hord : orderOf (2 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have hval : (1 / 6 : ℝ≥0) * ((12 : ℕ) : ℝ≥0) = 2 := by
    rw [show ((12 : ℕ) : ℝ≥0) = 12 from by norm_num, div_mul_eq_mul_div, one_mul]; norm_num
  have h := rs_boundary_epsMCA_eq (F := ZMod 13) (n := 12) (k := 8) (2 : ZMod 13) hord
    (by decide) (by norm_num) rfl (le_of_eq hval.symm) (by rw [hval]; norm_num)
  rw [h, ZMod.card]
  norm_num

end ProximityGap.BoundaryExactEpsF13
