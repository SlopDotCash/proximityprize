/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness

set_option maxHeartbeats 2000000

/-!
# A third exact boundary-band MCA value: `F_31`, `n = 15` (#389)

Third concrete instance of the boundary-band law `rs_boundary_epsMCA_eq` (`epsMCA = n/q`), after
`BoundaryExactEpsF19` (`9/19`) and `BoundaryExactEpsF13` (`12/13`).  For `RS[F_31, μ_15, 11]`
(`μ_15 = ⟨9⟩`, `9` a primitive 15th root of unity) at `δ = 2/15` (so `δ·n = 2 ∈ [2,3)`):

> **`epsMCA_boundary_F31_n15`** — `epsMCA(RS[F_31, μ_15, 11], 2/15) = 15/31`.

The three instances now exhibit the `n/q` law across `(n,q) ∈ {(9,19),(12,13),(15,31)}` — three
distinct fields and band parameters.  The value is the MCA *equality*, via the proven generic
sandwich; axiom-clean.
-/

open scoped NNReal ENNReal
open ProximityGap Code ProximityGap.CensusLowerBound ProximityGap.SmoothLadderInstance
  ProximityGap.MCAThresholdLedger ProximityGap.BoundarySupExactness

namespace ProximityGap.BoundaryExactEpsF31

instance primeFact_BoundaryExactEpsF31_1 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- **Exact boundary MCA value over `F_31`** (`n = 15`).  For `RS[F_31, μ_15, 11]`
(`μ_15 = ⟨9⟩`, `orderOf 9 = 15`) at `δ = 2/15`, the boundary-band law gives `epsMCA = 15/31`. -/
theorem epsMCA_boundary_F31_n15 :
    epsMCA (F := ZMod 31) (A := ZMod 31)
      (evalCode (smoothDom (9 : ZMod 31) 15) 11 : Set (Fin 15 → ZMod 31)) (2 / 15 : ℝ≥0)
      = (15 : ℝ≥0∞) / (31 : ℝ≥0∞) := by
  have hord : orderOf (9 : ZMod 31) = 15 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have hval : (2 / 15 : ℝ≥0) * ((15 : ℕ) : ℝ≥0) = 2 := by
    rw [show ((15 : ℕ) : ℝ≥0) = 15 from by norm_num, div_mul_cancel₀]; norm_num
  have h := rs_boundary_epsMCA_eq (F := ZMod 31) (n := 15) (k := 11) (9 : ZMod 31) hord
    (by decide) (by norm_num) rfl (le_of_eq hval.symm) (by rw [hval]; norm_num)
  rw [h, ZMod.card]
  norm_num

end ProximityGap.BoundaryExactEpsF31
