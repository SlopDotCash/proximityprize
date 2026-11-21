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

/-- The operational supremum in this interval. At the supremum the closed ball
includes the first failing Hamming shell. -/
theorem deltaStar (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hqD : Fintype.card F < D^2) (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F/D < n.choose (k+1)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
      (1/(D : ℝ≥0∞)) = 1 - ((k+1 : ℕ) : ℝ≥0)/n := by
  let r : ℝ≥0 := 1 - ((k+1 : ℕ) : ℝ≥0)/n
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast (NeZero.pos n)
  have hrat : ((k+1 : ℕ) : ℝ≥0)/n ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hkn)
  have hr : (1-r)*(n : ℝ≥0) = ((k+1 : ℕ) : ℝ≥0) := by
    rw [tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn.ne']
  have test := good_iff dom hk hkn hD hqD hlow hhigh
  simp_rw [← epsMCA_eq_mcaError] at test
  apply le_antisymm
  · apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
    apply lt_of_not_ge
    intro h
    exact lt_irrefl _ (hr ▸ (test r).mp h)
  · apply le_of_forall_lt_imp_le_of_dense
    intro x hx
    have hdiff : 1-r < 1-x :=
      tsub_lt_tsub_left_of_le (show r ≤ 1 from tsub_le_self) hx
    apply MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ (hx.le.trans tsub_le_self)
    apply (test x).mpr
    rw [← hr]
    exact mul_lt_mul_of_pos_right hdiff hn

end ProximityGap.CircuitBudgetRadius

#print axioms ProximityGap.CircuitBudgetRadius.good_iff

#print axioms ProximityGap.CircuitBudgetRadius.deltaStar
