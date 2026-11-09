/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld

/-!
# Dimension and degree for a positive-dimensional evaluation code

Normalize the symbolic dimension before instantiating large production parameters.
-/
namespace ProximityGap.Ownership

/-- Reconcile dimension `k` with polynomial degree at most `k - 1`, for positive `k`. -/
theorem evalCode_pred_eq_rsCode {p n k : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) (hk : 0 < k) :
    ArkLib.ProximityGap.KKH26.evalCode g n (k - 1) =
      ((ProximityGap.SpikeFloor.rsCode (smoothDom g n hg) k :
        Submodule (ZMod p) (Fin n → ZMod p)) : Set (Fin n → ZMod p)) := by
  have hdim : k - 1 + 1 = k := Nat.sub_add_cancel hk
  simpa only [hdim] using evalCode_eq_rsCode hg (k - 1)

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.evalCode_pred_eq_rsCode
