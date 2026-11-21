/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity

/-!
# Exact all-domain line-MCA radius in a binomial budget interval

Write N for choose(n,k+1) and B for floor(q/D). When floor(N/(k+1)) ≤ B < N
and q < D², every injective evaluation domain has its first failure at
n-k-1 errors for security 1/D. The radius test below concerns every real Hamming
radius, including the endpoint.
-/

open scoped NNReal ENNReal
open CoreDefinitions

namespace ProximityGap.CircuitBudgetRadius

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n k D : ℕ} [NeZero n]

/-- The security predicate at every radius from the adjacent detecting-circuit tests. -/
theorem good_iff (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hqD : Fintype.card F < D^2) (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F/D < n.choose (k+1)) (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤ 1/(D : ℝ≥0∞) ↔
      ((k+1 : ℕ) : ℝ≥0) < (1-δ)*n := by
  classical
  rw [← epsMCA_eq_mcaError]
  let C := (ReedSolomon.code dom k : Set (Fin n → F))
  constructor
  · intro h
    by_contra! ht
    have hplateau := epsMCA_eq_epsMCA_one_of_le_succ dom k (δ := δ)
      (by simpa using ht)
    rw [hplateau] at h
    have hsup : MCAThresholdLedger.mcaDeltaStar (F := F) C (1/(D : ℝ≥0∞)) = 1 :=
      le_antisymm (csSup_le' fun _ hmem => hmem.1)
        (MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl h)
    have hN := (BoundarySecurityBudget.deltaStar_eq_one_iff dom hk hkn hD hqD).mp hsup
    exact (not_le_of_gt hhigh) ((Nat.le_div_iff_mul_le hD).mpr hN)
  · intro hδ
    apply (epsMCA_le_of_badCount_le C δ (n.choose (k+1)/(k+1)) ?_).trans
      ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hD).mpr hlow)
    intro u
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr
    have hc := CircuitDensity.mca_count_mul_le dom k (k+2) δ (u 0) (u 1) (by omega)
      (fun S hS => by
        have hlt : ((k+1 : ℕ) : ℝ≥0) < S.card :=
          hδ.trans_le (by simpa using hS)
        exact_mod_cast hlt)
    rw [show k+2-1 = k+1 by omega, Nat.choose_succ_self_right, Fintype.card_fin] at hc
    convert hc using 2

end ProximityGap.CircuitBudgetRadius

#print axioms ProximityGap.CircuitBudgetRadius.good_iff
