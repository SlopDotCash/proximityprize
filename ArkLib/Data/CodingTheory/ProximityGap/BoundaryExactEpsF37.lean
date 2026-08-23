/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness

/-!
# A fourth exact boundary-band MCA value: `F_37`, `n = 18` (#389)

Fourth concrete instance of the boundary-band law `rs_boundary_epsMCA_eq` (`epsMCA = n/q`), after
`F_19` (`9/19`), `F_13` (`12/13`), `F_31` (`15/31`).  For `RS[F_37, μ_18, 14]` (`μ_18 = ⟨4⟩`,
`4` a primitive 18th root of unity) at `δ = 1/9` (so `δ·n = 2 ∈ [2,3)`):

> **`epsMCA_boundary_F37_n18`** — `epsMCA(RS[F_37, μ_18, 14], 1/9) = 18/37`.

The four instances now exhibit the `n/q` law across `(n,q) ∈ {(9,19),(12,13),(15,31),(18,37)}` —
four distinct fields and band parameters, the MCA *equality* in each via the proven generic sandwich.
Axiom-clean.
-/

set_option maxHeartbeats 2000000


open scoped NNReal ENNReal
open ProximityGap Code ProximityGap.CensusLowerBound ProximityGap.SmoothLadderInstance
  ProximityGap.MCAThresholdLedger ProximityGap.BoundarySupExactness

namespace ProximityGap.BoundaryExactEpsF37

instance primeFact_BoundaryExactEpsF37_1 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **Exact boundary MCA value over `F_37`** (`n = 18`).  For `RS[F_37, μ_18, 14]`
(`μ_18 = ⟨4⟩`, `orderOf 4 = 18`) at `δ = 1/9`, the boundary-band law gives `epsMCA = 18/37`. -/
theorem epsMCA_boundary_F37_n18 :
    epsMCA (F := ZMod 37) (A := ZMod 37)
      (evalCode (smoothDom (4 : ZMod 37) 18) 14 : Set (Fin 18 → ZMod 37)) (1 / 9 : ℝ≥0)
      = (18 : ℝ≥0∞) / (37 : ℝ≥0∞) := by
  have hord : orderOf (4 : ZMod 37) = 18 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have hval : (1 / 9 : ℝ≥0) * ((18 : ℕ) : ℝ≥0) = 2 := by
    rw [show ((18 : ℕ) : ℝ≥0) = 18 from by norm_num, div_mul_eq_mul_div, one_mul]; norm_num
  have h := rs_boundary_epsMCA_eq (F := ZMod 37) (n := 18) (k := 14) (4 : ZMod 37) hord
    (by decide) (by norm_num) rfl (le_of_eq hval.symm) (by rw [hval]; norm_num)
  rw [h, ZMod.card]
  norm_num

end ProximityGap.BoundaryExactEpsF37
