/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.JetSurfaceSafety

/-! # Quarter-rate MCA at a variable distance from the Johnson radius

For `n = 4*s*a` and dimension `s*a`, multiplicity `s` gives a uniform upper
bound at agreement `(2*s+1)*a`. Thus every fixed slack in this sequence has
an explicit finite-length bound linear in the domain size.
-/

set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.QuarterRateJohnsonSafety
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open HalfPredecessorBadEventRichPointBridge

private theorem triangle (q : ℕ) : 2*(∑ j : Fin q, (q-j.val)) = q*(q+1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.sub_zero,Fin.val_succ,Nat.succ_sub_succ_eq_sub,Nat.mul_add,ih]
    ring

/-- Clearing the two triangular sums proves positive interpolation dimension
uniformly in the scale `a`. -/
theorem jet_count (s a : ℕ) (hs : 0<s) (ha : 0<a) :
    let m := 2*s*(2*s+1)
    4*s*a*Fintype.card (JetRows m s) <
      Fintype.card (Monomials m (2*s) (s*a-1) (s*((2*s+1)*a))) := by
  dsimp only
  let m := 2*s*(2*s+1)
  let R := Fintype.card (JetRows m s)
  let V := Fintype.card (Monomials m (2*s) (s*a-1) (s*((2*s+1)*a)))
  change 4*s*a*R < V
  have hrows : R ≤ (∑ j : Fin s, (s-j.val))*(m+1) := by
    dsimp [R,JetRows]
    simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Finset.sum_mul]
    exact sum_le_sum fun j _ => Nat.mul_le_mul_left _ (Nat.sub_le ..)
  have hcols : ((∑ j : Fin (2*s+1), ((2*s+1)-j.val))*((m+1-2*s)*(s*a))) ≤ V := by
    dsimp [V,Monomials]
    simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Finset.sum_mul]
    apply sum_le_sum
    intro j _
    have hj := j.isLt
    have h₁ : m+1-2*s ≤ m+1-j.val := Nat.sub_le_sub_left (by omega) _
    have h₂ : ((2*s+1)-j.val)*(s*a) ≤ s*((2*s+1)*a)-j.val*(s*a-1) := by
      rw [Nat.sub_mul]
      have hc : (2*s+1)*(s*a) = s*((2*s+1)*a) := by ring
      rw [hc]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (Nat.sub_le ..)) _
    calc ((2*s+1)-j.val)*((m+1-2*s)*(s*a)) = (m+1-2*s)*(((2*s+1)-j.val)*(s*a)) := by ring
         _ ≤ _ := Nat.mul_le_mul h₁ h₂
  have hr := Nat.mul_le_mul_left (4*s*a*2) hrows
  have hc := Nat.mul_le_mul_left 2 hcols
  have hrt := triangle s
  have hct := triangle (2*s+1)
  have hsub : m+1-2*s = 4*s^2+1 := by
    have hm : m+1 = 4*s^2+1+2*s := by dsimp [m]; ring
    rw [hm,Nat.add_sub_cancel]
  rw [hsub] at hc
  have h₁ : 2*(4*s*a*R) ≤ 4*s*a*(s*(s+1))*(m+1) := by
    calc _ = (4*s*a*2)*R := by ring
         _ ≤ _ := hr
         _ = _ := by rw [← hrt]; ring
  have h₂ : ((2*s+1)*(2*s+1+1))*((4*s^2+1)*(s*a)) ≤ 2*V := by
    calc _ = 2*((∑ j : Fin (2*s+1), (2*s+1-j.val))*((4*s^2+1)*(s*a))) := by rw [← hct]; ring
         _ ≤ _ := hc
  have hd : 4*s*a*(s*(s+1))*(m+1) < ((2*s+1)*(2*s+1+1))*((4*s^2+1)*(s*a)) := by
    have hpos : 0 < 2*s*a*(s+1) := by positivity
    dsimp [m]
    nlinarith
  omega

private theorem transverse_cost (d m b : ℕ) (hb : 1 ≤ b) :
    let j := max 2 b
    j*(m+2*d*(m-1))+(j+2*d*(j-1))*m-j*(j+2*d*(j-1)) ≤ b*(8*m*(d+1)) := by
  let j := max 2 b
  change j*(_+_) + (_+_)*m - _ ≤ _
  have hj : j ≤ 2*b := by dsimp [j]; omega
  calc _ ≤ j*(m+2*d*m)+(j+2*d*j)*m := (Nat.sub_le ..).trans (by gcongr <;> omega)
       _ ≤ (2*b)*(m+2*d*m)+(2*b+2*d*(2*b))*m := by gcongr
       _ ≤ _ := by nlinarith

variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [Nonempty I] [DecidableEq I]

/-- At gap `1/(4*s)` inside the rate-quarter Johnson radius, every prescribed
injective domain and every pair of received words have the stated MCA error. -/
theorem epsMCA_le {p : ℕ} [CharP K p] (hp : p.Prime) (dom : I ↪ K) (δ : ℝ≥0)
    (s a : ℕ) (hs : 0<s) (ha : 0<a) (hn : Fintype.card I=4*s*a)
    (hchar : s*((2*s+1)*a) ≤ p)
    (htag : (2*s+1)*a ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊) :
    let m := 2*s*(2*s+1)
    _root_.ProximityGap.epsMCA (F:=K) (ReedSolomon.code dom (s*a) : Set (I → K)) δ ≤
      ((m+(2*s)*(8*m*(s*a)) : ℕ) : ℝ≥0∞)/(Fintype.card K : ℝ≥0∞) := by
  let m := 2*s*(2*s+1)
  let C₀ := 8*m*(s*a)
  have hk : s*a-1+1=s*a := by have := Nat.mul_pos hs ha; omega
  have hn' : Fintype.card I = 4*(s*a) := by rw [hn]; ring
  have hm : 2*s ≤ m := Nat.le_mul_of_pos_right _ (by positivity)
  have hbase : (2*s+1)*a ≤ s*((2*s+1)*a) := Nat.le_mul_of_pos_left _ hs
  have hc : 2*s+1 ≤ (2*s+1)*a := Nat.le_mul_of_pos_right _ ha
  have ht : s*a ≤ 2*s*a := Nat.mul_le_mul_right _ (by omega)
  have hle : s*a < (2*s+1)*a := by rw [Nat.add_mul]; omega
  have hprice : 4*(s*a)*m ≤ C₀ := by dsimp [C₀]; nlinarith
  have hnC : Fintype.card I ≤ C₀ := by
    rw [hn']; exact (Nat.le_mul_of_pos_right _ (by omega)).trans hprice
  refine _root_.ProximityGap.epsMCA_le_of_badCount_le _ _ _ (fun u => ?_)
  change (badScalars dom (s*a) δ u).card ≤ m+2*s*C₀
  rw [← hk]
  apply JetSurfaceSafety.bad_card_le hp dom δ u (s*a-1) ((2*s+1)*a) m (2*s) s C₀ hs (by omega)
    (by omega) (by rw [Nat.add_mul,hn']; nlinarith) htag hm (by omega) (by omega) (by omega) hchar
  · simpa only [hn,m] using jet_count s a hs ha
  · exact hnC
  · calc (Fintype.card I-(s*a-1))*m ≤ 4*(s*a)*m := Nat.mul_le_mul_right _ (hn' ▸ Nat.sub_le ..)
         _ ≤ C₀ := hprice
         _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · intro b hb _
    simpa only [hk,C₀] using transverse_cost (s*a-1) m b hb

#print axioms jet_count
#print axioms epsMCA_le
end ArkLib.ProximityGap.Frontier.QuarterRateJohnsonSafety
