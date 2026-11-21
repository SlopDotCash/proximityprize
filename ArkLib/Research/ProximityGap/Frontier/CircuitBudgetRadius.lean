/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity

/-!
# Exact all-domain line-MCA radius in a binomial budget interval

Write N for choose(n,k+1) and B for floor(q/D). When floor(N/(k+1)) ≤ B < N
and q < D², or when floor(N/(k+1)) ≤ B and q ≤ (D−1)N without a bit cap,
every injective evaluation domain has its first failure at
n-k-1 errors for security 1/D. The radius test below concerns every real Hamming
radius, including the endpoint.
-/

open scoped NNReal ENNReal
open CoreDefinitions

namespace ProximityGap.CircuitBudgetRadius

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n k D : ℕ} [NeZero n]

private theorem good_iff_of_bad_one (dom : Fin n ↪ F) (hk : 1 ≤ k) (hD : 0 < D)
    (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hbad : ¬ epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) 1 ≤ 1/(D : ℝ≥0∞))
    (δ : ℝ≥0) :
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
    exact hbad h
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

/-- The security predicate at every radius from the adjacent detecting-circuit tests. -/
theorem good_iff (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hqD : Fintype.card F < D^2) (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F/D < n.choose (k+1)) (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤ 1/(D : ℝ≥0∞) ↔
      ((k+1 : ℕ) : ℝ≥0) < (1-δ)*n := by
  apply good_iff_of_bad_one dom hk hD hlow _ δ
  intro h
  have hsup : MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
      (1/(D : ℝ≥0∞)) = 1 :=
    le_antisymm (csSup_le' fun _ hmem => hmem.1)
      (MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl h)
  have hN := (BoundarySecurityBudget.deltaStar_eq_one_iff dom hk hkn hD hqD).mp hsup
  exact (not_le_of_gt hhigh) ((Nat.le_div_iff_mul_le hD).mpr hN)

open Classical in
/-- If q ≤ (D−1) choose(n,k+1), the boundary fails the probability test in every
field size, including sizes far above the square of the security denominator. -/
theorem bad_one_of_card_le (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hhigh : Fintype.card F ≤ (D-1) * n.choose (k+1)) :
    ¬ epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) 1 ≤ 1/(D : ℝ≥0∞) := by
  let N := n.choose (k+1)
  let q := Fintype.card F
  let B := q/D
  let r : ℝ≥0 := 1 - ((k+1 : ℕ) : ℝ≥0)/n
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast NeZero.pos n
  have hrat : ((k+1 : ℕ) : ℝ≥0)/n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hkn)
  have hr : (1-r)*(Fintype.card (Fin n) : ℝ≥0) = ((k+1 : ℕ) : ℝ≥0) := by
    rw [Fintype.card_fin, tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn.ne']
  obtain ⟨P,hP⟩ := Ownership.boundary_production_failure dom hk
    (δ := r) (by rw [hr]; exact_mod_cast Nat.lt_succ_self k) hr.le
  let u : Code.WordStack F (Fin 2) (Fin n) := Code.finMapTwoWords
    (fun i => P.eval (dom i)) (fun i => (dom i)^k)
  have hu := mcaEvent_prob_le_epsMCA (F := F) (SpikeFloor.rsCode dom k : Set (Fin n → F)) r u
  rw [prob_uniform_eq_card_filter_div_card] at hu
  intro h
  have hgood := (epsMCA_mono (ReedSolomon.code dom k : Set (Fin n → F))
    (show r ≤ 1 by exact tsub_le_self)).trans h
  rw [← BoundarySecurityBudget.rsCode_eq_code] at hgood
  have hbound := hu.trans hgood
  simp only [ENNReal.coe_natCast] at hbound
  have hc := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hD).mp hbound
  have hM : N*q ≤ B*(q+N-1) := hP.trans (Nat.mul_le_mul_right _ hc)
  have hq : 0 < q := Fintype.card_pos
  have hnpos : 0 < N := Nat.choose_pos (by omega)
  have hBD : B*D ≤ q := Nat.div_mul_le_self ..
  have hlen : q+N-1 < D*N := by
    have hsum := Nat.add_le_add_right hhigh N
    change q+N ≤ (D-1)*N + N at hsum
    rw [← Nat.succ_mul, show (D-1).succ = D by omega] at hsum
    omega
  rcases Nat.eq_zero_or_pos B with hb | hb
  · rw [hb,zero_mul] at hM
    exact (not_le_of_gt (Nat.mul_pos hnpos hq)) hM
  · have hh := Nat.mul_lt_mul_of_pos_left hlen hb
    have hh' := Nat.mul_le_mul_right N hBD
    nlinarith

/-- The exact good-radius predicate in a binomial field-size interval without a fixed bit cap. -/
theorem wide_good_iff (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F ≤ (D-1) * n.choose (k+1)) (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤ 1/(D : ℝ≥0∞) ↔
      ((k+1 : ℕ) : ℝ≥0) < (1-δ)*n := by
  exact good_iff_of_bad_one dom hk hD hlow (bad_one_of_card_le dom hk hkn hD hhigh) δ

/-- The operational supremum in this interval. At the supremum the closed ball
includes the first failing Hamming shell. -/
private theorem deltaStar_of_test (dom : Fin n ↪ F) (hkn : k < n)
    (test : ∀ δ : ℝ≥0, mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤
      1/(D : ℝ≥0∞) ↔ ((k+1 : ℕ) : ℝ≥0) < (1-δ)*n) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
      (1/(D : ℝ≥0∞)) = 1 - ((k+1 : ℕ) : ℝ≥0)/n := by
  let r : ℝ≥0 := 1 - ((k+1 : ℕ) : ℝ≥0)/n
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast (NeZero.pos n)
  have hrat : ((k+1 : ℕ) : ℝ≥0)/n ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hkn)
  have hr : (1-r)*(n : ℝ≥0) = ((k+1 : ℕ) : ℝ≥0) := by
    rw [tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn.ne']
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

/-- The operational supremum in this interval. At the supremum the closed ball
includes the first failing Hamming shell. -/
theorem deltaStar (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hqD : Fintype.card F < D^2) (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F/D < n.choose (k+1)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
      (1/(D : ℝ≥0∞)) = 1 - ((k+1 : ℕ) : ℝ≥0)/n := by
  exact deltaStar_of_test dom hkn (good_iff dom hk hkn hD hqD hlow hhigh)

/-- The operational supremum in this interval. At the supremum the closed ball
includes the first failing Hamming shell. -/
theorem wide_deltaStar (dom : Fin n ↪ F) (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D)
    (hlow : n.choose (k+1)/(k+1) ≤ Fintype.card F/D)
    (hhigh : Fintype.card F ≤ (D-1) * n.choose (k+1)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
      (1/(D : ℝ≥0∞)) = 1 - ((k+1 : ℕ) : ℝ≥0)/n := by
  exact deltaStar_of_test dom hkn (wide_good_iff dom hk hkn hD hlow hhigh)

end ProximityGap.CircuitBudgetRadius

#print axioms ProximityGap.CircuitBudgetRadius.good_iff

#print axioms ProximityGap.CircuitBudgetRadius.deltaStar

#print axioms ProximityGap.CircuitBudgetRadius.wide_deltaStar
