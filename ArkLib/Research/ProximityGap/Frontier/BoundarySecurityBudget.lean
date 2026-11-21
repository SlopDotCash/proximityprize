/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProductionBoundaryFailure
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryGenericFarExact
import ArkLib.Research.ProximityGap.MCAPlateauWindow
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Exact line-MCA budget test at the first agreement count above the dimension

At an agreement threshold of k+1 the second-moment lower bound detects the first
integer exceeding a budget B whenever B² < q. Consequently for every finite field
of size q below D² the security test at error 1/D is exactly D * choose(n,k+1) ≤ q.
No separation condition on the full set of interpolation circuits is needed.
-/

open scoped NNReal ENNReal
open Code CoreDefinitions

namespace ProximityGap.BoundarySecurityBudget

open SpikeFloor Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- The campaign's evaluation code is the canonical Reed–Solomon submodule. -/
theorem rsCode_eq_code (dom : Fin n ↪ F) (k : ℕ) :
    rsCode dom k = ReedSolomon.code dom k := by
  ext w
  rw [ReedSolomon.mem_code_iff_eval]
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact ⟨P,hP,fun _ => rfl⟩
  · rintro ⟨P,hP,h⟩
    exact ⟨P,hP,funext fun i => (h i).symm⟩

/-- Dividing an integer bad count by the field size turns the security test into an integer budget. -/
theorem count_ratio_le_iff {a q D : ℕ} (hq : 0 < q) (hD : 0 < D) :
    (a : ℝ≥0∞) / q ≤ 1 / (D : ℝ≥0∞) ↔ a ≤ q / D := by
  have hq' : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq.ne'
  have hD' : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) hq')
    (ENNReal.div_ne_top (by simp) hD'), ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
  rw [div_le_div_iff₀ (by exact_mod_cast hq) (by exact_mod_cast hD), one_mul,
    Nat.le_div_iff_mul_le hD]
  norm_cast

private theorem count_le_of_second_moment {N q B M : ℕ} (hB : B^2 < q)
    (hM : M ≤ B) (hmoment : N*q ≤ M*(q+N-1)) : N ≤ B := by
  by_contra! hN
  have hq : 0 < q := by omega
  have hqB : B < q := by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) B]
  have h1 := (Nat.mul_le_mul_right (q+N-1) hM)
  have h2 := Nat.mul_le_mul (show B + 1 ≤ N by omega) (show q - B ≤ q - B by rfl)
  have h3 : q - B + B = q := Nat.sub_add_cancel hqB.le
  have h4 : q + N - 1 + 1 = q + N := by omega
  nlinarith [show N * (q - B + B) = N * q by rw [h3],
    show B * (q + N - 1 + 1) = B * (q + N) by rw [h4],
    show B * (q - B + B) = B * q by rw [h3]]

open Classical in
/-- At k+1 agreements the all-stack security predicate is decided by the number
of coordinate subsets, for every evaluation domain in every field of size below D². -/
theorem mcaError_le_one_div_iff [SampleableType F] (dom : Fin n ↪ F) {k D : ℕ}
    (hk : 1 ≤ k) (hD : 0 < D) (hqD : Fintype.card F < D^2) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1-δ)*(Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1-δ)*(Fintype.card (Fin n) : ℝ≥0) ≤ (k+1 : ℕ)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤ 1 / (D : ℝ≥0∞)
      ↔ n.choose (k+1) * D ≤ Fintype.card F := by
  rw [← rsCode_eq_code, ← epsMCA_eq_mcaError, ← Nat.le_div_iff_mul_le hD]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  let B := Fintype.card F / D
  have hBD : B < D := (Nat.div_lt_iff_lt_mul hD).mpr (by simpa [sq] using hqD)
  have hBq : B^2 < Fintype.card F := by
    by_cases hb : B = 0
    · simp [hb]
    · calc B^2 = B*B := sq _
           _ < B*D := Nat.mul_lt_mul_of_pos_left hBD (Nat.pos_of_ne_zero hb)
           _ ≤ Fintype.card F := Nat.div_mul_le_self _ _
  constructor
  · intro h
    obtain ⟨P,hP⟩ := boundary_production_failure dom hk hlo hhi
    let u : WordStack F (Fin 2) (Fin n) := finMapTwoWords
      (fun i => P.eval (dom i)) (fun i => (dom i)^k)
    have hu := mcaEvent_prob_le_epsMCA (F := F) (rsCode dom k : Set (Fin n → F)) δ u
    rw [prob_uniform_eq_card_filter_div_card] at hu
    apply count_le_of_second_moment hBq _ hP
    have hbound := hu.trans h
    simp only [ENNReal.coe_natCast] at hbound
    have hcount := (count_ratio_le_iff hq hD).mp hbound
    convert hcount using 1
    congr 1
  · intro h
    exact (epsMCA_le_boundary_choose dom hk hlo hhi).trans ((count_ratio_le_iff hq hD).mpr h)

/-- At the 128-bit prize tolerance and for fields of size below 2^256 the exact test is
valid irrespective of how large the full circuit family is relative to the field. -/
theorem mcaError_security128_iff [SampleableType F] (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (hq : Fintype.card F < 2^256) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1-δ)*(Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1-δ)*(Fintype.card (Fin n) : ℝ≥0) ≤ (k+1 : ℕ)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code dom k) (δ : ℝ) ≤ 1/(2^128 : ℝ≥0∞)
      ↔ n.choose (k+1)*2^128 ≤ Fintype.card F := by
  have h := mcaError_le_one_div_iff (D := 2^128) dom hk (by decide) (by convert hq using 1) hlo hhi
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- Exactly when the operational supremum is one, for a nontrivial rate and a
field below D². If it fails, a radius strictly below one already fails. -/
theorem deltaStar_eq_one_iff [SampleableType F] (dom : Fin n ↪ F) {k D : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (hD : 0 < D) (hqD : Fintype.card F < D^2) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (ReedSolomon.code dom k : Set (Fin n → F))
        (1/(D : ℝ≥0∞)) = 1 ↔ n.choose (k+1)*D ≤ Fintype.card F := by
  classical
  let r : ℝ≥0 := 1 - ((k+1 : ℕ) : ℝ≥0) / n
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast (NeZero.pos n)
  have hrat : ((k+1 : ℕ) : ℝ≥0) / n ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hkn)
  have hr : (1-r)*(Fintype.card (Fin n) : ℝ≥0) = ((k+1 : ℕ) : ℝ≥0) := by
    rw [Fintype.card_fin, tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn.ne']
  have hrlt : r < 1 := by
    apply tsub_lt_self (by norm_num)
    positivity
  have he := mcaError_le_one_div_iff dom hk hD hqD (δ := r)
    (by rw [hr]; exact_mod_cast Nat.lt_succ_self k) hr.le
  rw [← epsMCA_eq_mcaError] at he
  have hplateau := epsMCA_eq_epsMCA_one_of_le_succ dom k (by simpa using hr.le)
  constructor
  · intro hone
    by_contra hlarge
    have hbad := lt_of_not_ge (fun hgood => hlarge (he.mp hgood))
    have hbound := MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ hbad
    rw [hone] at hbound
    exact (not_le_of_gt hrlt) hbound
  · intro h
    have hgood := he.mpr h
    rw [hplateau] at hgood
    apply le_antisymm _ (MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl hgood)
    apply csSup_le
    · exact ⟨1, le_rfl, hgood⟩
    · exact fun _ hr' => hr'.1

end ProximityGap.BoundarySecurityBudget

#print axioms ProximityGap.BoundarySecurityBudget.mcaError_le_one_div_iff
#print axioms ProximityGap.BoundarySecurityBudget.mcaError_security128_iff

#print axioms ProximityGap.BoundarySecurityBudget.deltaStar_eq_one_iff
