/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine

/-!
# Scaling first-order interpolation slot counts

A strict integer inequality at a reference length implies a shifted interpolation
slot surplus at every positive integral multiple. The exception estimate below
is quadratic in the domain length under the displayed bounds on its parameters.
-/

namespace ProximityGap.ScaledFirstOrderSecurity

open ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions Finset

private def rowSlots (n m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), n * (∑ s ∈ range m,
    min (m-s) (min t s + 1 - (t-M))) * (h+1-t)

private def columnSlots (k A m M μ h : ℕ) : ℕ :=
  ∑ t ∈ range (μ+1), ∑ _b ∈ range (min t M+1), (m*A-k*t)*(h+1-t)

private theorem row_le (b n D A m M μ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M μ (b*n) 1 h ≤ b * rowSlots n m M μ h := by
  unfold firstOrderCurveShiftedRowSlotBound rowSlots
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t _
  rw [one_mul, ← mul_assoc b, ← mul_assoc b]
  gcongr
  unfold firstOrderGradedRankBound
  apply sum_le_sum
  intro s _
  unfold firstOrderGradedSourceCount
  split_ifs <;> simp

private theorem column_le (b k A m M μ h : ℕ) :
    b * columnSlots k A m M μ h ≤
      firstOrderCurveShiftedHeightSlotCount (b*k-1) (b*A) m M μ 1 h := by
  unfold firstOrderCurveShiftedHeightSlotCount columnSlots
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro t _
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro j _
  rw [one_mul, ← mul_assoc b, Nat.mul_sub b (m*A) (k*t)]
  apply Nat.mul_le_mul_right
  apply tsub_le_tsub
  · exact (Nat.le_add_right _ j).trans_eq (by ac_rfl)
  · exact (Nat.mul_le_mul_right t (Nat.sub_le (b*k) 1)).trans_eq (by ac_rfl)

private theorem scaled_slots {b n k A m M μ h : ℕ} (hb : 0 < b)
    (hcert : rowSlots n m M μ h < columnSlots k A m M μ h) :
    firstOrderCurveShiftedRowSlotBound (b*k-1) (b*A) m M μ (b*n) 1 h <
      firstOrderCurveShiftedHeightSlotCount (b*k-1) (b*A) m M μ 1 h :=
  (row_le ..).trans_lt ((Nat.mul_lt_mul_of_pos_left hcert hb).trans_le (column_le ..))

private theorem exception_le {n D A h μ M : ℕ} (hn : 1 ≤ n) (hDn : D ≤ n)
    (hθ : agreementIncidenceRatio n D A ≤ 8) (hh : h ≤ 1500) (hμ0 : 0 < μ) (hμ : μ ≤ 80)
    (hstairs : stageStaircase μ M ≤ 30000) :
    firstOrderExceptionConstant (agreementIncidenceRatio n D A) n D h μ M ≤
      (2 : ℝ)^37 * (n : ℝ)^2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hh' : (h : ℝ) ≤ 1500 := by exact_mod_cast hh
  have hμ' : (μ : ℝ) ≤ 80 := by exact_mod_cast hμ
  have htail : ((2*μ-1 : ℕ) : ℝ) ≤ 160 := by exact_mod_cast (show 2*μ-1 ≤ 160 by omega)
  have habs : ((n-D-1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show n-D-1 ≤ n by omega)
  have hθ0 : 0 ≤ agreementIncidenceRatio n D A := by
    unfold agreementIncidenceRatio
    positivity
  have hT : 0 ≤ stageStaircase μ M := by unfold stageStaircase; positivity
  unfold firstOrderExceptionConstant ordinaryTailCharge
  rw [ite_eq_right_iff.mpr (fun h => (hμ0.ne' h).elim)]
  calc _ ≤ 160*1500 + (8:ℝ)*(1500+80+4*n*80*1500) + n*80 +
        (24*(n:ℝ)^2*1500+8*n)*8^2*30000 + 4*n*n*8*30000 := by gcongr
       _ ≤ _ := by
         nlinarith [sq_nonneg ((n:ℝ)-1), mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg (α:=ℝ) n)]

end ProximityGap.ScaledFirstOrderSecurity
