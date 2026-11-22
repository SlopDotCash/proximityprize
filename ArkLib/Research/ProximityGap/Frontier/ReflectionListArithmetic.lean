/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReflectionListBound

/-! # The uniform row weight at half rate -/
namespace ProximityGap.ReflectionListSampling

private abbrev m (e : ℕ) := e.choose 2-e/2

private theorem pair_growth {e : ℕ} (he : 3≤e) : m (e+1) ≤ 2*m e := by
  by_cases h4 : 4≤e
  · have est : 3*e ≤ e*(e-1) := by
      rw [Nat.mul_comm 3 e]
      exact Nat.mul_le_mul_left _ (by omega)
    have lower : e≤m e := by dsimp [m];rw [Nat.choose_two_right];omega
    dsimp only [m] at lower ⊢
    rw [show (e+1).choose 2=e+e.choose 2 by rw [Nat.choose_succ_succ' e 1,Nat.choose_one_right]]
    omega
  · obtain rfl : e=3 := by omega
    decide

/-- The last error shell minimizes the count whenever r≤k or the central
binomial coefficient bounds the cost of the earlier shells. -/
theorem endpoint_payment_wide {k r : ℕ}
    (room : r≤k ∨ m (r+1)*(k+2) ≤ 2*(2*k+2).choose (k+1)) :
    RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)) := by
  let w (e : ℕ) := m e * (k+3+r-e).choose (r+2-e)
  have step (e : ℕ) (lo : 3≤e) (hi : e≤r) (enough : r+2≤k+e) : w (e+1) ≤ w e := by
    let n := k+3+r-(e+1)
    let j := r+2-(e+1)
    have val : w e=m e*(n+1).choose (j+1) := by
      dsimp only [w,n,j]
      rw [show k+3+r-(e+1)+1=k+3+r-e by omega,show r+2-(e+1)+1=r+2-e by omega]
    have small : j<n/2 := by dsimp only [j,n];omega
    have grow := Nat.choose_le_succ_of_lt_half_left small
    have twice : 2*n.choose j≤(n+1).choose (j+1) := by
      rw [Nat.choose_succ_succ'];omega
    rw [val]
    change m (e+1)*n.choose j ≤ m e*(n+1).choose (j+1)
    calc _ ≤ (2*m e)*n.choose j := Nat.mul_le_mul_right _ (pair_growth lo)
         _ = m e*(2*n.choose j) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ twice
  intro e lo hi
  have descend (a b : ℕ) (ha : 3≤a) (hb : a≤b) (stop : b≤r+1) (enough : r+2≤k+a) : w b≤w a := by
    induction b,hb using Nat.le_induction with
    | base => exact le_rfl
    | succ j h ih => exact (step j (by omega) (by omega) (by omega)).trans (ih (by omega))
  have bot : w (r+1) = m (r+1)*(k+2) := by
    dsimp [w]
    rw [show k+3+r-(r+1)=k+2 by omega,show r+2-(r+1)=1 by omega,Nat.choose_one_right]
  have rwgt : m (r+1)*(k+2) ≤ w e := by
    by_cases enough : r+2≤k+e
    · rw [←bot]
      exact descend e (r+1) lo hi le_rfl enough
    · have cap := room.resolve_left (by omega)
      have bg := Nat.choose_le_choose (k+1) (show 2*k+2≤k+3+r-e by omega)
      have pair2 : 2≤m e := by
        have est : e*2 ≤ e*(e-1) := Nat.mul_le_mul_left e (by omega)
        dsimp only [m]
        rw [Nat.choose_two_right]
        omega
      apply cap.trans
      rw [show w e=m e*(k+3+r-e).choose (k+1) by
        dsimp only [w]
        rw [← Nat.choose_symm (show r+2-e≤k+3+r-e by omega),show k+3+r-e-(r+2-e)=k+1 by omega]]
      exact Nat.mul_le_mul pair2 bg
  change (k+2)*(m (r+1)*(k+1)) ≤ (m e)*((k+3+r-e).choose (r+2-e)*(k+1))
  calc _ = (m (r+1)*(k+2))*(k+1) := by ring
       _ ≤ w e*(k+1) := Nat.mul_le_mul_right _ rwgt
       _ = _ := by simp [w,mul_assoc]

/-- At and above half rate, the row comparison requires only r≤k. -/
theorem endpoint_payment {k r : ℕ} (hr : r≤k) :
    RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)) :=
  endpoint_payment_wide (Or.inl hr)

/-- The endpoint payment is automatic for all four sponsor dimensions once
the smallest dimension exceeds 6143. -/
theorem sponsor_payment {k r : ℕ} (size : 6144≤k) (rate : r+1≤16*k) :
    RowBudget k r (((r+1).choose 2-(r+1)/2)*(k+1)) := by
  apply endpoint_payment_wide (Or.inr ?_)
  have cm := Nat.choose_le_middle 4 (2*k+2)
  rw [show (2*k+2)/2=k+1 by omega] at cm
  have kpow := (Nat.pow_le_pow_left (show k≤2*k+2+1-4 by omega) 4).trans
    (Nat.pow_sub_le_descFactorial (2*k+2) 4)
  rw [Nat.descFactorial_eq_factorial_mul_choose,show Nat.factorial 4=24 by decide] at kpow
  have low := kpow.trans (Nat.mul_le_mul_left 24 cm)
  have md : m (r+1) ≤ (16*k)^2 := by
    apply le_trans _ (Nat.pow_le_pow_left rate 2)
    dsimp only [m]
    apply (Nat.sub_le _ _).trans
    rw [Nat.choose_two_right,pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have size' : 6144*k^3 ≤ k*k^3 := Nat.mul_le_mul_right _ size
  have cost := Nat.mul_le_mul md (show k+2≤2*k by omega)
  nlinarith

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.endpoint_payment
