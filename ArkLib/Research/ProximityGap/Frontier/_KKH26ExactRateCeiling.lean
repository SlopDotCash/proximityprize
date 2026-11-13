/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SubCeilingLadder
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# The exact-rate endpoint of the KKH26 degree window

`SubCeilingLadder.subceiling_epsMCA_lower_bound` decouples the KKH26 witness spread from
the original degree `(r - 2) * m`: it applies to every degree `D` with
`(r - 2) * m ≤ D < (r - 1) * m`.  The largest such degree is
`D = (r - 1) * m - 1`, whose Reed--Solomon dimension is exactly `(r - 1) * m`.

This file packages that endpoint and its operational `mcaDeltaStar` ceiling.  Choosing
`r - 1` to be the desired dyadic rate times `2^μ` therefore removes the former `+1`
dimension mismatch without changing the KKH26 bad-line construction.
-/

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-- The endpoint degree `(r - 1) * m - 1` lies in the degree-decoupled KKH26 window. -/
theorem exactRate_degree_window {m r : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r) :
    (r - 2) * m ≤ (r - 1) * m - 1 ∧
      (r - 1) * m - 1 < (r - 1) * m := by
  have hstep : (r - 2) * m < (r - 1) * m :=
    (Nat.mul_lt_mul_right hm).2 (by omega)
  have hpos : 0 < (r - 1) * m := Nat.mul_pos (by omega) hm
  omega

/-- **Exact-rate KKH26 witness spread.**  The KKH26 bad-scalar lower bound holds for the
largest code degree below the direction degree.  This code has dimension `(r - 1) * m`,
not `(r - 2) * m + 1`. -/
theorem kkh26_exactRate_epsMCA_lower_bound
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) :
    ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ENNReal) / (p : ENNReal)
      ≤ epsMCA (F := ZMod p)
          (evalCode g n ((r - 1) * m - 1))
          (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) := by
  obtain ⟨hD₁, hD₂⟩ := exactRate_degree_window hm hr2
  exact subceiling_epsMCA_lower_bound hμ hm hn hg hp hr2 hr hD₁ hD₂

/-- **Exact-rate KKH26 operational ceiling.**  Every target below the bad-scalar mass
forces the operational threshold of the dimension-`(r - 1) * m` code down to the KKH26
boundary `1 - r / 2^μ`. -/
theorem kkh26_exactRate_mcaDeltaStar_le
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ENNReal)
    (hεstar : εstar <
      ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ENNReal) / (p : ENNReal)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 1) * m - 1)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_exactRate_epsMCA_lower_bound hμ hm hn hg hp hr2 hr))

/-- The exact-rate endpoint really is the Reed--Solomon code of dimension `(r - 1) * m`
on the smooth domain. -/
theorem exactRate_evalCode_eq_rsCode
    {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p} {m r : ℕ}
    (hm : 1 ≤ m) (hr2 : 2 ≤ r) (hg : orderOf g = n) :
    evalCode g n ((r - 1) * m - 1) =
      ((ProximityGap.SpikeFloor.rsCode
          (ProximityGap.Ownership.smoothDom g n hg) ((r - 1) * m) :
          Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p)) := by
  have hpos : 0 < (r - 1) * m := Nat.mul_pos (by omega) hm
  have hdim : (r - 1) * m - 1 + 1 = (r - 1) * m := by omega
  simpa only [hdim] using
    ProximityGap.Ownership.evalCode_eq_rsCode hg ((r - 1) * m - 1)

end ArkLib.ProximityGap.KKH26

#print axioms ArkLib.ProximityGap.KKH26.exactRate_degree_window
#print axioms ArkLib.ProximityGap.KKH26.kkh26_exactRate_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.kkh26_exactRate_mcaDeltaStar_le
#print axioms ArkLib.ProximityGap.KKH26.exactRate_evalCode_eq_rsCode
