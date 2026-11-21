/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FirstOrderChargeFloor
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveHeightCounting

/-! # Exact boundary for the first-order height certificate at total jet degree one

At degree one the first graded rank is one in multiplicity one and twice
the multiplicity minus two otherwise. Multiplicity two realizes the exact
boundary 3A ≥ 2n+D, as soon as the height pays for the constant-term deficit.
-/
set_option autoImplicit false
namespace ProximityGap.FirstOrderDegreeOneBoundary
open Finset ReedSolomon.HiddenDerivative

private theorem strip_active {D A m s : ℕ} (hDA : D < A) (hm : 0 < m) (hs : s < m) :
    s + (D-1) < m*A := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h := Nat.le_mul_of_pos_right u (by omega : 0 < A)
  rw [Nat.succ_mul]
  omega

private theorem rank_zero {D A m M : ℕ} (hDA : D < A) :
    firstOrderGradedRankBound D A m M 0 = m := by
  unfold firstOrderGradedRankBound
  calc _ = ∑ _s ∈ range m, 1 := by
         apply sum_congr rfl
         intro s hs
         have hs := mem_range.mp hs
         have h : s < m*A := lt_of_lt_of_le hs (Nat.le_mul_of_pos_right m (by omega))
         simp [firstOrderGradedSourceCount,h,show 1 ≤ m-s by omega]
    _ = _ := by simp

/-- The actual first graded rank with a positive first-derivative cap. -/
theorem rank_one {D A m M : ℕ} (hDA : D < A) (hm : 0 < m) (hM : 0 < M) :
    firstOrderGradedRankBound D A m M 1 = if m = 1 then 1 else 2*(m-1) := by
  unfold firstOrderGradedRankBound
  have hsum : (∑ s ∈ range m, min (m-s) (firstOrderGradedSourceCount D A m M s 1)) =
      ∑ s ∈ range m, min (m-s) (min 1 s + 1) := by
    apply sum_congr rfl
    intro s hs
    simp [firstOrderGradedSourceCount,strip_active hDA hm (mem_range.mp hs),show 1-M=0 by omega]
  rw [hsum]
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  cases u with
  | zero => simp
  | succ v =>
    rw [sum_range_succ, sum_range_succ']
    have hs : (∑ x ∈ range v, min (v+1+1-(x+1)) (min 1 (x+1)+1)) = 2*v := by
      calc _ = ∑ _x ∈ range v, 2 := by
             apply sum_congr rfl
             intro x hx
             have hx := mem_range.mp hx
             omega
        _ = _ := by simp [Nat.mul_comm]
    rw [hs]
    simp only [Nat.succ_eq_add_one, Nat.sub_zero]
    rw [ite_eq_right (by omega)]
    omega

/-- At total jet degree zero the two height counts are independent of the derivative cap. -/
theorem slots_zero (D A m M n ℓ h : ℕ) (hDA : D < A) :
    firstOrderCurveShiftedRowSlotBound D A m M 0 n ℓ h = n*m*(h+1) ∧
    firstOrderCurveShiftedHeightSlotCount D A m M 0 ℓ h = m*A*(h+1) := by
  simp [firstOrderCurveShiftedRowSlotBound,firstOrderCurveShiftedHeightSlotCount,rank_zero hDA]

private theorem slots_one {D A m M : ℕ} (hDA : D < A) (hm : 0 < m) (hM : 0 < M)
    (n ℓ h : ℕ) :
    firstOrderCurveShiftedRowSlotBound D A m M 1 n ℓ h =
      n*m*(h+1) + n*(if m = 1 then 1 else 2*(m-1))*(h+1-ℓ) ∧
    firstOrderCurveShiftedHeightSlotCount D A m M 1 ℓ h =
      m*A*(h+1) + (2*(m*A-D)+1)*(h+1-ℓ) := by
  have hle : D ≤ m*A := hDA.le.trans (Nat.le_mul_of_pos_left A hm)
  have hsub := Nat.sub_add_cancel hle
  simp only [firstOrderCurveShiftedRowSlotBound,firstOrderCurveShiftedHeightSlotCount,
    sum_range_succ,sum_range_zero,zero_add,rank_zero hDA,rank_one hDA hm hM,Nat.mul_zero,
    Nat.mul_one, Nat.sub_zero, Nat.zero_min, Nat.add_zero, Nat.min_eq_left hM,
    show m*A+1-D = m*A-D+1 by omega]
  constructor
  · trivial
  · ring

/-- A strict degree-one slot surplus requires 3A ≥ 2n+D, even at arbitrary challenge weight. -/
theorem three_agreement_le {n D A m M ℓ h : ℕ} (hDA : D < A) (hAn : A ≤ n)
    (hm : 0 < m) (hM : 0 < M)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M 1 n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M 1 ℓ h) : 2*n+D ≤ 3*A := by
  obtain ⟨hr,hc⟩ := slots_one hDA hm hM n ℓ h
  rw [hr,hc] at hs
  let rank := if m = 1 then 1 else 2*(m-1)
  have h0 : m*A ≤ n*m := (Nat.mul_le_mul_left m hAn).trans_eq (Nat.mul_comm ..)
  have hx := Nat.sub_add_cancel h0
  have htotal : n*m + n*rank < m*A + (2*(m*A-D)+1) := by
    by_contra! he
    apply (not_lt_of_ge ?_) hs
    change _ ≤ n*m*(h+1) + n*rank*(h+1-ℓ)
    have he' : 2*(m*A-D)+1 ≤ (n*m-m*A) + n*rank := by omega
    have hheight : h+1-ℓ ≤ h+1 := Nat.sub_le _ _
    calc _ ≤ m*A*(h+1) + ((n*m-m*A) + n*rank)*(h+1-ℓ) :=
           Nat.add_le_add_left (Nat.mul_le_mul_right _ he') _
      _ ≤ m*A*(h+1) + (n*m-m*A)*(h+1) + n*rank*(h+1-ℓ) := by
            rw [Nat.add_mul, Nat.add_assoc]
            gcongr
      _ = _ := by rw [← Nat.add_mul, Nat.add_comm (m*A), hx]
  have hle : D ≤ m*A := hDA.le.trans (Nat.le_mul_of_pos_left A hm)
  have hsub := Nat.sub_add_cancel hle
  by_cases hm1 : m = 1
  · subst m
    simp [rank] at htotal
    omega
  · obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ m)
    by_contra! h
    have ht := Nat.mul_le_mul_left m (by omega : 3*A+1 ≤ 2*n+D)
    have hn := Nat.mul_le_mul_left v (hDA.le.trans hAn)
    simp only [rank, ite_eq_right hm1] at htotal
    rw [hv] at htotal ht hsub
    have hh : 2+v-1 = v+1 := by omega
    rw [hh] at htotal
    nlinarith

/-- Agreement beyond the degree-one certificate boundary is within Johnson. -/
theorem johnson_of_degree_one {n D A m M ℓ h : ℕ} (hDA : D < A) (hAn : A ≤ n)
    (hm : 0 < m) (hM : 0 < M)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M 1 n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M 1 ℓ h) : n*D ≤ A^2 := by
  have h := three_agreement_le hDA hAn hm hM hs
  have hsq := Nat.mul_le_mul h h
  have hnon : D ≤ n := hDA.le.trans hAn
  have a := Nat.sub_add_cancel hnon
  have b := Nat.sub_add_cancel (by omega : D ≤ 4*n)
  nlinarith [Nat.zero_le ((n-D)*(4*n-D))]

/-- For a line challenge and total jet degree one, the agreement inequality
is sufficient. Multiplicity two and height 2(n−A)+1 realize a strict surplus. -/
theorem degree_one_exact {n D A M : ℕ} (hDA : D < A) (hAn : A ≤ n) (hM : 0 < M) :
    (∃ m h : ℕ, 0 < m ∧ firstOrderCurveShiftedRowSlotBound D A m M 1 n 1 h <
      firstOrderCurveShiftedHeightSlotCount D A m M 1 1 h) ↔ 2*n+D ≤ 3*A := by
  constructor
  · rintro ⟨m,h,hm,hs⟩
    exact three_agreement_le hDA hAn hm hM hs
  · intro hg
    let h := 2*(n-A)+1
    refine ⟨2,h,by decide,?_⟩
    obtain ⟨hr,hc⟩ := slots_one hDA (m := 2) (by decide) hM n 1 h
    rw [hr,hc]
    simp only [show (2:ℕ) ≠ 1 by decide,ite_false,Nat.reduceSub,Nat.mul_one,Nat.add_sub_cancel]
    have hcut := Nat.sub_add_cancel (show D ≤ 2*A by omega)
    have hdiff := Nat.sub_add_cancel hAn
    have hh := Nat.mul_le_mul_right (2*h) hg
    have hs := congrArg (fun z : ℕ => 2*z*h) hcut
    change n*2*(h+1)+n*2*h < 2*A*(h+1)+(2*(2*A-D)+1)*h
    have hh' : h + 2*A = 2*n+1 := by dsimp [h]; omega
    nlinarith

/-- A strict shifted certificate below Johnson has total jet degree at least two. -/
theorem two_le_degree_of_beyond_johnson {n D A m M μ ℓ h : ℕ}
    (hDA : D < A) (hAn : A ≤ n) (hm : 0 < m) (hM : 0 < M) (hb : A^2 < n*D)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) : 2 ≤ μ := by
  by_contra! hsmall
  interval_cases μ
  · obtain ⟨hr,hc⟩ := slots_zero D A m M n ℓ h hDA
    rw [hr,hc] at hs
    exact (not_lt_of_ge (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left m hAn).trans_eq (Nat.mul_comm ..)))) hs
  · exact (not_lt_of_ge (johnson_of_degree_one hDA hAn hm hM hs)) hb

/-- The optimized exceptional count has a quadratic charge throughout the
beyond-Johnson region for every successful positive-cap shifted certificate. -/
theorem positive_cap_charge_floor {n D A m M μ ℓ h : ℕ}
    (hDA : D < A) (hAn : A ≤ n) (hm : 0 < m) (hM : 0 < M) (hb : A^2 < n*D)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    ((n-A : ℕ) : ℝ)*(1+regularTaylorExponent D : ℕ) ≤
      maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h μ M :=
  FirstOrderChargeFloor.optimized_floor hDA hAn (two_le_degree_of_beyond_johnson hDA hAn hm hM hb hs) hM

/-- At the half-rate production example the entire positive-cap family exceeds
2⁵⁸ as soon as the actual column/row test succeeds. -/
theorem half_rate_positive_cap_barrier {m M μ ℓ h : ℕ} (hm : 0 < m) (hM : 0 < M)
    (hs : firstOrderCurveShiftedRowSlotBound (2^29-1) (89*2^23) m M μ (2^30) ℓ h <
      firstOrderCurveShiftedHeightSlotCount (2^29-1) (89*2^23) m M μ ℓ h) :
    (2:ℝ)^58 < maxMinFirstOrderExceptionCharge
      (agreementIncidenceRatio (2^30) (2^29-1) (89*2^23))
      (2^30) (2^29-1) (89*2^23) h μ M :=
  FirstOrderChargeFloor.half_rate_floor h μ M
    (two_le_degree_of_beyond_johnson (by decide) (by decide) hm hM (by decide) hs) hM

#print axioms half_rate_positive_cap_barrier
#print axioms degree_one_exact
#print axioms positive_cap_charge_floor
#print axioms rank_one
#print axioms johnson_of_degree_one
end ProximityGap.FirstOrderDegreeOneBoundary
