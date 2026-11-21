/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FirstOrderDegreeOneBoundary
import Mathlib.Algebra.Order.Chebyshev

/-! # The zero-derivative-cap interpolation test cannot pass beyond Johnson

The unweighted row layers have size n(m−t)₊ and the source layers (mA−Dt)₊.
The integral triangle count includes its final incomplete layer. Dominance of
every prefix, followed by Abel's inequality, covers every cap and height.
-/
set_option autoImplicit false
namespace ProximityGap.FirstOrderZeroCapJohnson
open Finset ReedSolomon.HiddenDerivative

/-- Without derivatives, exactly the blocks with t ≤ s < m contribute one row. -/
theorem rank_zero_cap {D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (t : ℕ) :
    firstOrderGradedRankBound D A m 0 t = m-t := by
  unfold firstOrderGradedRankBound
  calc _ = ∑ s ∈ range m, (if t ≤ s then 1 else 0) := by
         apply sum_congr rfl
         intro s hs
         have hsm := mem_range.mp hs
         by_cases ht : t ≤ s
         · have ha : s+(D-1)*t < m*A := calc
              _ ≤ s+(D-1)*s := Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
              _ = D*s := by
                have h := congrArg (fun a : ℕ => a*s) (Nat.sub_add_cancel hD)
                nlinarith
              _ < D*m := Nat.mul_lt_mul_of_pos_left hsm hD
              _ ≤ m*A := (Nat.mul_le_mul_right m hDA).trans_eq (Nat.mul_comm ..)
           simp [firstOrderGradedSourceCount,ha,ht,show 1 ≤ m-s by omega]
         · simp only [firstOrderGradedSourceCount,Nat.sub_zero,ite_eq_right ht]
           split_ifs <;> omega
    _ = ((range m).filter (fun s => t ≤ s)).card := sum_boole ..
    _ = (Ico t m).card := by congr 1; ext; simp [and_comm]
    _ = _ := Nat.card_Ico ..

private def ramp (x d T : ℕ) : ℕ := ∑ t ∈ range T, (x-d*t)

private theorem ramp_id (x d T : ℕ) (h : ∀ t < T, d*t ≤ x) :
    2*ramp x d T + d*T*T = 2*T*x + d*T := by
  induction T with
  | zero => simp [ramp]
  | succ T ih =>
    have hi := ih (fun t ht => h t (by omega))
    have hc := Nat.sub_add_cancel (h T (by omega))
    have hs : ramp x d (T+1) = ramp x d T + (x-d*T) := sum_range_succ ..
    rw [hs]
    nlinarith

private theorem ramp_stable {x d s t : ℕ} (hst : s ≤ t) (hstop : x ≤ d*s) :
    ramp x d t = ramp x d s := by
  symm
  apply sum_subset_zero_on_sdiff (range_mono hst)
  · intro i hi
    have hi : s ≤ i := by simpa using (mem_sdiff.mp hi).2
    exact Nat.sub_eq_zero_of_le (hstop.trans (Nat.mul_le_mul_left _ hi))
  · simp

private theorem ramp_upper_cut {x d T : ℕ} (hd : 0 < d) :
    ramp x d T ≤ ramp x d (x/d+1) := by
  rcases le_total T (x/d+1) with hs | hs
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hs) (by intros; omega)
  · exact (ramp_stable hs (Nat.lt_mul_div_succ x hd).le).le

private theorem ramp_integral (x D u r : ℕ) (hx : x = D*u+r) (hr : r < D) :
    2*D*ramp x D (u+1) = x^2+D*x+r*(D-r) := by
  subst x
  have h := ramp_id (D*u+r) D (u+1) (fun t ht =>
    (Nat.mul_le_mul_left D (show t ≤ u by omega)).trans (by omega))
  have hmul := congrArg (fun v : ℕ => D*v) h
  have hrem := congrArg (fun v : ℕ => r*v) (Nat.sub_add_cancel hr.le)
  nlinarith

private theorem full_source_bound {m A D T : ℕ} (hD : 0 < D) (hDA : D ≤ A) :
    2*D*ramp (m*A) D T ≤ m*(m+1)*A^2 := by
  let r := m*A%D
  let u := m*A/D
  have hmod : m*A = D*u+r := by simpa [r,u,Nat.add_comm] using (Nat.mod_add_div (m*A) D).symm
  have hr : r < D := Nat.mod_lt _ hD
  have hsplit : m*A = m*(A-D)+m*D := by rw [← Nat.mul_add,Nat.sub_add_cancel hDA]
  have hrle : r ≤ m*(A-D) := by
    dsimp [r]
    rw [hsplit,Nat.add_mul_mod_self_right]
    exact Nat.mod_le ..
  have hres : r*(D-r) ≤ m*A*(A-D) :=
    (Nat.mul_le_mul hrle ((Nat.sub_le D r).trans hDA)).trans_eq (by ring)
  have hA := congrArg (fun v : ℕ => m*A*v) (Nat.sub_add_cancel hDA)
  calc _ ≤ 2*D*ramp (m*A) D (u+1) := Nat.mul_le_mul_left _ (ramp_upper_cut hD)
    _ = (m*A)^2+D*(m*A)+r*(D-r) := ramp_integral _ _ _ _ hmod hr
    _ ≤ _ := by nlinarith

/-- Every prefix of the ordinary interpolation triangle has no surplus throughout
the closed Johnson region A² ≤ nD, including any partial final source layer. -/
theorem prefix_bound {n D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n)
    (hJ : A^2 ≤ n*D) (T : ℕ) :
    (∑ t ∈ range T, (m*A-D*t)) ≤ ∑ t ∈ range T, n*(m-t) := by
  change ramp (m*A) D T ≤ _
  rw [← mul_sum]
  change ramp (m*A) D T ≤ n * (∑ t ∈ range T, (m-t))
  have he (j : ℕ) : ∑ t ∈ range j, (m-t) = ramp m 1 j := by simp [ramp]
  rw [he]
  have hright := Nat.le_total T m
  rcases hright with hTm | hmT
  · cases T with
    | zero => simp [ramp]
    | succ j =>
      have hleft := ramp_id (m*A) D (j+1) (fun t ht =>
        (Nat.mul_le_mul hDA (by omega : t ≤ m)).trans_eq (Nat.mul_comm ..))
      have hright := ramp_id m 1 (j+1) (by intros; omega)
      have hDn := hDA.trans hAn
      obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hDn
      have hmean : 2*A ≤ n+D := by
        by_contra! hh
        have hlt := Nat.mul_lt_mul_of_pos_right hh hD
        nlinarith [sq_nonneg ((A : ℤ)-(D : ℤ))]
      have havg := Nat.mul_le_mul_left m hmean
      have hN : n*j+2*m*A ≤ D*j+2*m*n := by
        rw [hv] at *
        nlinarith [Nat.mul_le_mul_left v (by omega : j ≤ m)]
      have hNj := Nat.mul_le_mul_left (j+1) hN
      have hr := congrArg (fun z : ℕ => n*z) hright
      nlinarith
  · rw [ramp_stable hmT (by simp : m ≤ 1*m)]
    have hfull := full_source_bound (m := m) (T := T) hD hDA
    have hright := ramp_id m 1 m (by intros; omega)
    have hstep := Nat.mul_le_mul_left (m*(m+1)) hJ
    have hmul := congrArg (fun z : ℕ => n*D*z) hright
    exact Nat.le_of_mul_le_mul_left (show (2*D)*ramp (m*A) D T ≤ (2*D)*(n*ramp m 1 m) by nlinarith) (by omega)

/-- No total degree or height makes the zero-first-derivative-cap shifted slot
certificate pass when A² ≤ nD. -/
theorem no_surplus {n D A m : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n)
    (hJ : A^2 ≤ n*D) (μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A m 0 μ ℓ h ≤
      firstOrderCurveShiftedRowSlotBound D A m 0 μ n ℓ h := by
  simp only [firstOrderCurveShiftedHeightSlotCount,firstOrderCurveShiftedRowSlotBound,Nat.min_zero,
    Nat.zero_add,sum_range_one,Nat.add_zero,rank_zero_cap hD hDA]
  let f (t : ℕ) : ℤ := (m*A-D*t : ℕ)
  let c (t : ℕ) : ℤ := (n*(m-t) : ℕ)
  let w (t : ℕ) : ℤ := (h+1-ℓ*t : ℕ)
  have hw : 0 ≤ w := fun _ => Int.natCast_nonneg _
  have ha : AntitoneOn w (Set.Iio (μ+1)) := by
    intro i _ j _ hij
    dsimp [w]
    exact_mod_cast Nat.sub_le_sub_left (Nat.mul_le_mul_left ℓ hij) (h+1)
  have hb := Finset.sum_mul_le_sum_mul_of_sum_range_le (f := f) (c := c)
    (fun T _ => (by dsimp [f,c]; exact_mod_cast prefix_bound hD hDA hAn hJ (m := m) T)) hw ha
  dsimp [f,c,w] at hb
  exact_mod_cast hb

private theorem surplus_height (c r : ℕ → ℕ) (ℓ μ : ℕ)
    (hs : (∑ i ∈ range (μ+1), r i) < ∑ i ∈ range (μ+1), c i) :
    ∃ h : ℕ, (∑ i ∈ range (μ+1), r i*(h+1-ℓ*i)) <
      ∑ i ∈ range (μ+1), c i*(h+1-ℓ*i) := by
  let R := ∑ i ∈ range (μ+1), r i
  let C := ∑ i ∈ range (μ+1), c i
  have hRC : R+1 ≤ C := hs
  let h := ℓ*μ*C
  have hbase : ℓ*μ ≤ h+1 := (Nat.le_mul_of_pos_right _ (show 0 < C by omega)).trans (by omega)
  refine ⟨h,?_⟩
  calc _ ≤ R*(h+1) := by
         dsimp [R]
         rw [sum_mul]
         exact sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le ..)
    _ < C*(h+1-ℓ*μ) := by
         have hd := congrArg (fun a : ℕ => C*a) (Nat.sub_add_cancel hbase)
         have hscaled := Nat.mul_le_mul_right (h+1) hRC
         have he : h = ℓ*μ*C := rfl
         nlinarith
    _ ≤ _ := by
         dsimp [C]
         rw [sum_mul]
         apply sum_le_sum
         intro i hi
         exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left
           (Nat.mul_le_mul_left ℓ (Nat.le_of_lt_succ (mem_range.mp hi))) _)

/-- On the safe side of Johnson ordinary interpolation does have a strict slot surplus,
at some finite height, for each prescribed challenge weight. -/
theorem zero_cap_exact {n D A : ℕ} (hD : 0 < D) (hDA : D ≤ A) (hAn : A ≤ n) (ℓ : ℕ) :
    (∃ (m μ h : ℕ), 0 < m ∧ firstOrderCurveShiftedRowSlotBound D A m 0 μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m 0 μ ℓ h) ↔ n*D < A^2 := by
  constructor
  · rintro ⟨m,μ,h,_,hs⟩
    exact lt_of_not_ge fun hj => (not_lt_of_ge (no_surplus hD hDA hAn hj μ ℓ h)) hs
  · intro hJ
    let m := D*(n+1)
    let μ := A*(n+1)
    have hm : 0 < m := by dsimp [m]; positivity
    have hmμ : m ≤ μ := Nat.mul_le_mul_right _ hDA
    have hx : m*A = D*μ+0 := by dsimp [m,μ]; ring
    have hsrc := ramp_integral (m*A) D μ 0 hx hD
    simp only [Nat.zero_mul,Nat.add_zero] at hsrc
    have hrows := ramp_id m 1 m (by intros; omega)
    have hs : n*ramp m 1 m < ramp (m*A) D (μ+1) := by
      have hl : D*n < m := by dsimp [m]; nlinarith
      have hgap := Nat.mul_le_mul_left m (show n*D+1 ≤ A^2 from hJ)
      have hmid : n*D*(m+1) < m*A^2+D*A := by nlinarith
      have hcert := Nat.mul_lt_mul_of_pos_left hmid hm
      have hr := congrArg (fun x : ℕ => n*D*x) hrows
      exact Nat.lt_of_mul_lt_mul_left (show (2*D)*(n*ramp m 1 m) <
        (2*D)*ramp (m*A) D (μ+1) by nlinarith)
    have hcrit : (∑ i ∈ range (μ+1), n*(m-i)) < ∑ i ∈ range (μ+1), (m*A-D*i) := by
      rw [← mul_sum]
      have hcut := ramp_stable (x := m) (d := 1) (s := m) (t := μ+1) (by omega)
        (by simp)
      simp only [ramp,Nat.one_mul] at hcut
      rw [hcut]
      exact (by simpa only [ramp,Nat.one_mul] using hs)
    obtain ⟨h,hh⟩ := surplus_height (fun t => m*A-D*t) (fun t => n*(m-t)) ℓ μ hcrit
    refine ⟨m,μ,h,hm,?_⟩
    simpa only [firstOrderCurveShiftedRowSlotBound,firstOrderCurveShiftedHeightSlotCount,
      Nat.min_zero,Nat.zero_add,sum_range_one,Nat.add_zero,rank_zero_cap hD hDA] using hh

private theorem slots_at_zero_multiplicity {D : ℕ} (hD : 0 < D) (A M μ ℓ h : ℕ) :
    firstOrderCurveShiftedHeightSlotCount D A 0 M μ ℓ h = 0 := by
  unfold firstOrderCurveShiftedHeightSlotCount
  apply sum_eq_zero
  intro t _
  apply sum_eq_zero
  intro b hb
  have hbt := (Nat.le_of_lt_succ (mem_range.mp hb)).trans (min_le_left ..)
  have hbd := hbt.trans (Nat.le_mul_of_pos_left t hD)
  simp [Nat.sub_eq_zero_of_le hbd]

/-- At or beyond Johnson, a successful shifted certificate must pay the optimized
quadratic exception charge, for arbitrary multiplicity, first-derivative cap, total
degree, challenge weight and height. -/
theorem unrestricted_charge_floor {n D A m M μ ℓ h : ℕ} (hD : 0 < D) (hDA : D < A)
    (hAn : A ≤ n) (hJ : A^2 ≤ n*D)
    (hs : firstOrderCurveShiftedRowSlotBound D A m M μ n ℓ h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ ℓ h) :
    ((n-A : ℕ) : ℝ)*(1+regularTaylorExponent D : ℕ) ≤
      maxMinFirstOrderExceptionCharge (agreementIncidenceRatio n D A) n D A h μ M := by
  have hm : 0 < m := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, slots_at_zero_multiplicity hD] at hs
    omega
  have hM : 0 < M := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz] at hs
    exact (not_lt_of_ge (no_surplus hD hDA.le hAn hJ μ ℓ h)) hs
  apply FirstOrderChargeFloor.optimized_floor hDA hAn _ hM
  by_contra! hsmall
  interval_cases μ
  · obtain ⟨hr,hc⟩ := FirstOrderDegreeOneBoundary.slots_zero D A m M n ℓ h hDA
    rw [hr,hc] at hs
    exact (not_lt_of_ge (Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left m hAn).trans_eq (Nat.mul_comm ..)))) hs
  · have ht := FirstOrderDegreeOneBoundary.three_agreement_le hDA hAn hm hM hs
    have hsquare := Nat.mul_le_mul ht ht
    have hDn : D < n := hDA.trans_le hAn
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_lt hDn
    rw [hv] at hsquare hJ
    nlinarith

/-- The numerical half-rate test exceeds a 2⁵⁸ charge at radius 39/128, for
every choice of the certificate parameters whose shifted slot count succeeds. -/
theorem half_rate_unrestricted_barrier {m M μ ℓ h : ℕ}
    (hs : firstOrderCurveShiftedRowSlotBound (2^29-1) (89*2^23) m M μ (2^30) ℓ h <
      firstOrderCurveShiftedHeightSlotCount (2^29-1) (89*2^23) m M μ ℓ h) :
    (2:ℝ)^58 < maxMinFirstOrderExceptionCharge
      (agreementIncidenceRatio (2^30) (2^29-1) (89*2^23))
      (2^30) (2^29-1) (89*2^23) h μ M := by
  apply lt_of_lt_of_le _ (unrestricted_charge_floor (by decide) (by decide) (by decide) (by decide) hs)
  norm_num [regularTaylorExponent]

#print axioms zero_cap_exact
#print axioms unrestricted_charge_floor
#print axioms half_rate_unrestricted_barrier
#print axioms prefix_bound
#print axioms no_surplus
end ProximityGap.FirstOrderZeroCapJohnson
