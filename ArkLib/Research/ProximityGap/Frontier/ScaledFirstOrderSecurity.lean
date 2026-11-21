/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.ListBound
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound

/-!
# First-order certificates beyond Johnson for all four prize rates

A strict integer inequality at a reference length implies a shifted interpolation
slot surplus at every positive integral multiple. The resulting line bound is
uniform over the evaluation domain. All constants below are independent of the
field and the length.
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
  rw [ite_eq_right hμ0.ne']
  calc _ ≤ 160*1500 + (8:ℝ)*(1500+80+4*n*80*1500) + n*80 +
        (24*(n:ℝ)^2*1500+8*n)*8^2*30000 + 4*n*n*8*30000 := by gcongr
       _ ≤ _ := by
         nlinarith [sq_nonneg ((n:ℝ)-1),
           mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg (α:=ℝ) n)]

private theorem security_of_slots {p b k A m M μ h : ℕ} [Fact p.Prime]
    [SampleableType (ZMod p)] (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAn : A ≤ 128)
    (hgap : 128 + 7*k ≤ 8*A) (hh : h ≤ 1500) (hμ0 : 0 < μ) (hμ : μ ≤ 80)
    (hM : M ≤ 128) (hstairs : stageStaircase μ M ≤ 30000)
    (hslots : rowSlots 128 m M μ h < columnSlots k A m M μ h)
    (hp : 2^165*(b*128)^2 ≤ p) (dom : Fin (b*128) ↪ ZMod p) {r : ℝ}
    (hr : r ≤ 1 - (A:ℝ)/128) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  let D := b*k-1
  have hbk : 2 ≤ b*k := by nlinarith
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hsucc : b*k = D+1 := by dsimp [D]; omega
  have hAp : b*k < b*A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hDA : D < b*A := by omega
  have hAn' := Nat.mul_le_mul_left b hAn
  have hn : 1 ≤ b*128 := by omega
  have hDn : D ≤ b*128 := by omega
  have hθ : agreementIncidenceRatio (b*128) D (b*A) ≤ 8 := by
    unfold agreementIncidenceRatio
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < b*A-D by omega))).mpr
    have hbg := Nat.mul_le_mul_left b hgap
    have eq₁ := Nat.sub_add_cancel hDn
    have eq₂ := Nat.sub_add_cancel hDA.le
    exact_mod_cast (show b*128-D ≤ 8*(b*A-D) by nlinarith)
  have hnp : b*128 < p := by
    have hsq : b*128 ≤ (b*128)^2 := Nat.le_self_pow (by decide) _
    nlinarith
  have hchar : ringChar (ZMod p) = 0 ∨ max D M < ringChar (ZMod p) := by
    right
    rw [ZMod.ringChar_zmod_n]
    omega
  let B := (2:ℝ)^37 * ((b*128 : ℕ) : ℝ)^2
  have hline : LineExactAgreementBound dom (b*k) (b*A) B := by
    apply lineExactAgreementBound_of_exactCorrelatedPair
    intro f g
    obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (F := ZMod p) (k := b*k) hD hsucc.le dom f g (scaled_slots hb hslots)
    obtain ⟨ex,_,_,hc,hfit⟩ := cert.exists_exceptional_hybrid hsucc hD hDA hchar
    exact ⟨ex,hc.trans (exception_le hn hDn hθ hh hμ0 hμ hstairs),hfit⟩
  have hth : b*A ≤ ⌈(Fintype.card (Fin (b*128)) : ℝ)*(1-r)⌉₊ := by
    calc b*A = ⌈((b*A:ℕ):ℝ)⌉₊ := (Nat.ceil_natCast (R := ℝ) _).symm
         _ ≤ _ := Nat.ceil_mono ?_
    rw [Fintype.card_fin, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    have hw := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) b)
    linarith
  refine (mcaError_affineLine_le_of_exactAgreement dom B hline r hth).trans ?_
  rw [ZMod.card]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ (by exact_mod_cast (Fact.out : p.Prime).pos) (by norm_num : (0:ℝ)<2^128)).mpr
  have h : (2:ℝ)^165*((b*128:ℕ):ℝ)^2 ≤ p := by exact_mod_cast hp
  dsimp [B]
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem four_slot_certificates :
    rowSlots 128 43 12 59 1426 < columnSlots 64 89 43 12 59 1426 ∧
    rowSlots 128 35 15 66 1217 < columnSlots 32 61 35 15 66 1217 ∧
    rowSlots 128 26 13 67 1181 < columnSlots 16 42 26 13 67 1181 ∧
    rowSlots 128 22 13 79 1321 < columnSlots 8 29 22 13 79 1321 := by
  decide

/-- At every length 128b and every prescribed prime-field domain, the four
listed radii give 128-bit line MCA security when p ≥ 2^165 n². -/
theorem four_rates {b p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)] (hb : 0 < b)
    (hp : 2^165*(b*128)^2 ≤ p) (dom : Fin (b*128) ↪ ZMod p) :
    let good := fun (k : ℕ) (r : ℝ) => mcaError (AffineLineGenerator (ZMod p))
      (code dom (b*k)) r ≤ ENNReal.ofReal (1/(2:ℝ)^128)
    good 64 (39/128) ∧ good 32 (67/128) ∧ good 16 (86/128) ∧ good 8 (99/128) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := four_slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · exact security_of_slots hb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num [stageStaircase]) h₁ hp dom (by norm_num)
  · exact security_of_slots hb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num [stageStaircase]) h₂ hp dom (by norm_num)
  · exact security_of_slots hb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num [stageStaircase]) h₃ hp dom (by norm_num)
  · exact security_of_slots hb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num [stageStaircase]) h₄ hp dom (by norm_num)

/-- The agreement counts used above lie strictly below the finite-length
Johnson threshold √(n(k−1)) at all four dimensions, including b=1. -/
theorem below_finite_johnson {b : ℕ} (hb : 0 < b) :
    (b*89)^2 < (b*128)*(b*64-1) ∧ (b*61)^2 < (b*128)*(b*32-1) ∧
    (b*42)^2 < (b*128)*(b*16-1) ∧ (b*29)^2 < (b*128)*(b*8-1) := by
  have hpos : (0:ℤ) ≤ b-1 := by omega
  have hb2 : (b:ℤ) ≤ (b:ℤ)^2 := by nlinarith [mul_nonneg hpos (Int.natCast_nonneg b)]
  refine ⟨?_,?_,?_,?_⟩
  all_goals zify [show 1 ≤ b*64 by omega, show 1 ≤ b*32 by omega,
    show 1 ≤ b*16 by omega, show 1 ≤ b*8 by omega]; nlinarith


private theorem weight_le_scaled {b : ℕ} (hb : 0 < b) (k μ M : ℕ) :
    firstOrderListWeight (b*k) μ M ≤ b * firstOrderListWeight k μ M := by
  induction μ generalizing M with
  | zero => simp [firstOrderListWeight]
  | succ μ ih =>
    cases M with
    | zero =>
      simp only [firstOrderListWeight, Nat.mul_add]
      have h := ih 0
      nlinarith
    | succ M =>
      simp only [firstOrderListWeight, Nat.mul_add]
      have h := ih M
      nlinarith [Nat.mul_le_mul_left (μ+1) hb]

private theorem list_of_slots {p b k A m M μ h C : ℕ} [Fact p.Prime]
    (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAn : A ≤ 128)
    (hμ : μ < 128) (hcost : firstOrderListWeight k μ M ≤ C*(A-k))
    (hslots : rowSlots 128 m M μ h < columnSlots k A m M μ h)
    (dom : Fin (b*128) ↪ ZMod p) :
    Code.Lambda (code dom (b*k) : Set (Fin (b*128) → ZMod p)) (1-(A:ℝ)/128) ≤
      ((C*(b*128):ℕ):ℕ∞) := by
  classical
  let g := ((A-k:ℕ):ℝ)/128
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hbR : (b:ℝ) ≠ 0 := by positivity
  have h₁ : capacityAgreementThreshold g (b*128) (b*k) = b*A := by
    have he : g*((b*128:ℕ):ℝ) = ((b*(A-k):ℕ):ℝ) := by dsimp [g]; push_cast; ring
    rw [capacityAgreementThreshold, he, Nat.ceil_natCast, Nat.mul_sub, Nat.add_sub_of_le]
    exact Nat.mul_le_mul_left b hkA.le
  have h₂ : capacityRadius g (b*128) (b*k) = 1-(A:ℝ)/128 := by
    unfold capacityRadius g
    rw [Nat.cast_sub hkA.le]
    push_cast
    field_simp
    ring
  rw [← h₂, ← Nat.ceil_natCast (R := ℝ) (C*(b*128))]
  apply lambda_le_ceil_of_closePolynomialSet_bound hg (by omega)
  intro f
  rw [h₁]
  let T := @closePolynomialSet (ZMod p) _ (Classical.decEq _) _ dom f (b*k) (b*A)
  have hbk : 2 ≤ b*k := by nlinarith
  have hdiff : 0 < b*A-b*k+1 := Nat.succ_pos _
  have hnp : b*128 ≤ p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have hlt : b*k < b*A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hAn' := Nat.mul_le_mul_left b hAn
  have hchar : ringChar (ZMod p) = 0 ∨ max (b*k-1) μ < ringChar (ZMod p) := by
    right; rw [ZMod.ringChar_zmod_n]; omega
  have bound (S : Finset (Polynomial (ZMod p))) (hST : (↑S : Set _) ⊆ T) : S.card ≤ C*(b*128) := by
    have hpoint (P : Polynomial (ZMod p)) (hP : P ∈ S) :
        P.degree < b*k ∧ b*A ≤ ({i : Fin (b*128) | P.eval (dom i) = f i} : Set _).ncard := by
      have h := hST hP
      refine ⟨h.1, h.2.trans_eq ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext i
      simp [polynomialAgreementSet]
    have hbound := finite_firstOrder_list_bound_of_heightSlotCount_sharp
      (D := b*k-1) (K := b*k) (by omega) (by omega) dom f
      (scaled_slots hb hslots) hbk le_rfl (by omega) hlt.le hchar S hpoint
    have hcross := (le_div_iff₀ (by exact_mod_cast hdiff)).mp hbound
    have hN : S.card * (b*A-b*k+1) ≤ (b*128) * firstOrderListWeight (b*k) μ M := by
      exact_mod_cast hcross
    have hw := (weight_le_scaled hb k μ M).trans (Nat.mul_le_mul_left b hcost)
    have hfactor : firstOrderListWeight (b*k) μ M ≤ C*(b*A-b*k+1) := by
      rw [← Nat.mul_sub]
      nlinarith
    exact Nat.le_of_mul_le_mul_right
      (le_trans hN (by simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using
        Nat.mul_le_mul_left (b*128) hfactor)) hdiff
  have hfin : T.Finite := Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := C*(b*128)) bound
  refine ⟨hfin, ?_⟩
  have h := bound hfin.toFinset (by simp)
  rw [← Set.ncard_eq_toFinset_card _ hfin] at h
  exact_mod_cast h

set_option maxRecDepth 100000 in
/-- The same radii give a scalar list-size bound linear in n, even when the
prime field is only large enough to contain the evaluation domain. -/
theorem four_list_bounds {p b : ℕ} [Fact p.Prime] (hb : 0 < b)
    (dom : Fin (b*128) ↪ ZMod p) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (code dom (b*k) : Set (Fin (b*128) → ZMod p)) r ≤ ((C*(b*128):ℕ):ℕ∞)
    bounded 64 (39/128) 173373 ∧ bounded 32 (67/128) 113975 ∧
      bounded 16 (86/128) 58872 ∧ bounded 8 (99/128) 52349 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := four_slot_certificates
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat, show (1-(89:ℝ)/128) = 39/128 by norm_num] using
      list_of_slots (C:=173373) hb (by decide) (by decide) (by decide) (by decide) (by decide) h₁ dom
  · simpa only [Nat.cast_ofNat, show (1-(61:ℝ)/128) = 67/128 by norm_num] using
      list_of_slots (C:=113975) hb (by decide) (by decide) (by decide) (by decide) (by decide) h₂ dom
  · simpa only [Nat.cast_ofNat, show (1-(42:ℝ)/128) = 86/128 by norm_num] using
      list_of_slots (C:=58872) hb (by decide) (by decide) (by decide) (by decide) (by decide) h₃ dom
  · simpa only [Nat.cast_ofNat, show (1-(29:ℝ)/128) = 99/128 by norm_num] using
      list_of_slots (C:=52349) hb (by decide) (by decide) (by decide) (by decide) (by decide) h₄ dom

end ProximityGap.ScaledFirstOrderSecurity

#print axioms ProximityGap.ScaledFirstOrderSecurity.four_rates

#print axioms ProximityGap.ScaledFirstOrderSecurity.below_finite_johnson

#print axioms ProximityGap.ScaledFirstOrderSecurity.four_list_bounds
