/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ScaledSecondOrderPrimeCuts
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-! # All-width order-two list bounds on prescribed prime-field domains

Constant received curves have challenge height zero. An order-two partition
profile then requires only a strict column surplus. The canonical direct-jet
bound gives a quadratic list bound over the rational-function field, which
controls every finite interleaving width over the original prime field.
-/
namespace ProximityGap.SecondOrderAllWidthLists
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential Polynomial Finset
open PartitionOriginCertificate SecondOrderOriginBlocks SecondOrderBlockCounts

structure Profile where
  k : ℕ
  A : ℕ
  m : ℕ
  W : ℕ
  v : ℕ
  r : ℕ
  N : ℕ
  listFactor : ℕ
  deriving DecidableEq

/-- The four prescribed list profiles in descending rate order. -/
def profiles : Fin 4 → Profile
  | 0 => ⟨2048,2803,107,45,146,2149848,8805812660,13190740336⟩
  | 1 => ⟨1024,1876,107,67,196,3982844,16314045580,8440423840⟩
  | 2 => ⟨512,1258,99,74,243,3879239,15889778888,6515819463⟩
  | 3 => ⟨256,851,72,63,239,1438025,5891028352,2395867711⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 90000000 in
private theorem counts (i : Fin 4) : let c := profiles i
    blockBudget c.m c.W c.v = c.r ∧ sourceBudget c.k (c.m*c.A) c.W c.v = c.N := by
  dsimp only
  rw [← SecondOrderPrimeFieldCuts.blockSum_eq (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    SecondOrderPrimeFieldCuts.sourceBudget_eq (by fin_cases i <;> decide)]
  fin_cases i <;> decide +kernel

private theorem weight (i : Fin 4) : let c := profiles i
    (c.v*(1+2*c.k*(c.v-1)))^2 ≤ c.listFactor*(c.A-c.k)^2 := by
  fin_cases i <;> decide

/-- The direct-jet list charge at every positive scale. -/
private theorem scaled_cost (i : Fin 4) {b : ℕ} (hb : 0 < b) : let c := profiles i
    (c.v:ℚ)^2 * (((b*4096*(1+2*(b*c.k)*(c.v-1)):ℕ):ℚ) / (b*c.A-b*c.k+1:ℕ))^2 ≤
    (c.listFactor*(b*4096)^2:ℕ) := by
  let c := profiles i
  have hA : c.k<c.A := by fin_cases i <;> decide
  have hbase := weight i
  have hbu : 1+2*(b*c.k)*(c.v-1) ≤ b*(1+2*c.k*(c.v-1)) := by nlinarith
  have hden : b*c.A-b*c.k+1 = b*(c.A-c.k)+1 := by rw [Nat.mul_sub]
  have denpos : 0 < b*(c.A-c.k) := Nat.mul_pos hb (Nat.sub_pos_of_lt hA)
  have cros : c.v*(b*4096*(1+2*(b*c.k)*(c.v-1))) ≤ (b*4096)*b*(c.v*(1+2*c.k*(c.v-1))) := by
    calc _ ≤ c.v*(b*4096*(b*(1+2*c.k*(c.v-1)))) := by gcongr
         _ = _ := by ring
  have square : (c.v*(b*4096*(1+2*(b*c.k)*(c.v-1))))^2 ≤
      c.listFactor*(b*4096)^2*(b*c.A-b*c.k+1)^2 := calc
    _ ≤ ((b*4096)*b*(c.v*(1+2*c.k*(c.v-1))))^2 := Nat.pow_le_pow_left cros 2
    _ = (b*4096)^2*b^2*(c.v*(1+2*c.k*(c.v-1)))^2 := by ring
    _ ≤ (b*4096)^2*b^2*(c.listFactor*(c.A-c.k)^2) := by gcongr
    _ = c.listFactor*(b*4096)^2*(b*(c.A-c.k))^2 := by ring
    _ ≤ _ := by rw [hden]; gcongr; omega
  dsimp only
  rw [div_pow,← mul_div_assoc,div_le_iff₀ (by positivity)]
  exact_mod_cast (show c.v^2*(b*4096*(1+2*(b*c.k)*(c.v-1)))^2 ≤ _ by
    simpa only [mul_pow] using square)

/-- Over characteristic zero or characteristic at least the block length,
the complete list at the closed profile radius is bounded quadratically. -/
theorem scalar {F : Type} [Field F] {b : ℕ} (hb : 0<b) (i : Fin 4)
    (hchar : ringChar F=0 ∨ b*4096≤ringChar F) (dom : Fin (b*4096) ↪ F) :
    let c := profiles i
    Code.Lambda (code dom (b*c.k) : Set (Fin (b*4096) → F)) (1-(c.A:ℝ)/4096) ≤
      ((c.listFactor*(b*4096)^2:ℕ):ℕ∞) := by
  classical
  let c := profiles i
  let g : ℝ := ((c.A-c.k:ℕ):ℝ)/4096
  have hk : 0<c.k := by fin_cases i <;> decide
  have hkA : c.k≤c.A := by fin_cases i <;> decide
  have hD := Nat.mul_pos hb hk
  have hk3 : 3 ≤ b*c.k := (by fin_cases i <;> decide : 3 ≤ c.k).trans (Nat.le_mul_of_pos_left _ hb)
  have hc : c.m*c.A ≤ c.k*(c.v+1) := by fin_cases i <;> decide
  have hcut : b*(c.m*c.A) ≤ b*c.k*(c.v+1) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left b hc
  have hv := jet_cap (W := c.W) hcut
  have rank := origin_rank (F := F) (m := c.m) hD hv
  rw [(counts i).1] at rank
  have lower := source_card_lower (L := b*(c.m*c.A)) (W := c.W) (v := c.v) hD
  rw [ScaledSecondOrderPrimeCuts.source_scaled,(counts i).2] at lower
  have surplus : 4096*c.r<c.N := by fin_cases i <;> decide
  have s : b*4096*c.r < b*c.N := by simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_left surplus hb
  have threshold : capacityAgreementThreshold g (b*4096) (b*c.k) = b*c.A := by
    have he : g*((b*4096:ℕ):ℝ) = ((b*(c.A-c.k):ℕ):ℝ) := by dsimp [g]; push_cast; ring
    rw [capacityAgreementThreshold,he,Nat.ceil_natCast,Nat.mul_sub,Nat.add_sub_of_le (Nat.mul_le_mul_left b hkA)]
  have rad : capacityRadius g (b*4096) (b*c.k) = 1-(c.A:ℝ)/4096 := by
    dsimp [capacityRadius,g]
    rw [Nat.cast_sub hkA]
    push_cast
    field_simp
    ring
  change Code.Lambda (code dom (b*c.k) : Set (Fin (b*4096) → F)) (1-(c.A:ℝ)/4096) ≤ _
  rw [←rad,←Nat.ceil_natCast (R := ℝ) (c.listFactor*(b*4096)^2)]
  apply lambda_le_ceil_of_closePolynomialSet_bound (show 0≤g by dsimp [g]; positivity) (by omega)
  intro f
  rw [threshold]
  obtain ⟨cert⟩ := certificate_of_origin_rank (ℓ := 0) hD
    (show ((b*(c.m*c.A):ℕ):ℝ)≤(c.m*(b*c.A):ℕ) by exact_mod_cast (show b*(c.m*c.A)≤c.m*(b*c.A) by rw [Nat.mul_left_comm]))
    (Nat.le_succ _) dom (fun x => Polynomial.C (f x)) (by intro x; simp)
    hv rank (s.trans_le lower)
  have ch : ringChar F=0 ∨ max (b*c.k-1) (max 2 c.v) < ringChar F := by
    apply hchar.imp_right
    intro hp
    have h₁ : c.k≤4096 := by fin_cases i <;> decide
    have h₂ : c.v<4096 := by fin_cases i <;> decide
    have h₃ := Nat.mul_le_mul_left b h₁
    omega
  obtain ⟨finite,bound⟩ := close_list_bound_of_curve_certificate_directJetCoarse dom f cert hD
    (Nat.mul_le_mul_left b hkA) ch
  rw [max_eq_left hk3] at bound
  refine ⟨finite,?_⟩
  exact_mod_cast bound.trans (scaled_cost i hb)

/-- Over every prime field admitting the supplied sites, the same bound
works simultaneously for every center and each interleaving width. -/
theorem all_width {p b : ℕ} [Fact p.Prime] (hb : 0<b) (i : Fin 4)
    (dom : Fin (b*4096) ↪ ZMod p) (width : ℕ) :
    let c := profiles i
    Code.Lambda (Code.interleavedCodeSet (κ := Fin width) (code dom (b*c.k) : Set (Fin (b*4096) → ZMod p)))
      (1-(c.A:ℝ)/4096) ≤ ((c.listFactor*(b*4096)^2:ℕ):ℕ∞) := by
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hp : b*4096≤p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have ch : ringChar (RatFunc (ZMod p))=p := ringChar.eq _ p
  exact (Lambda_interleaved_le_ratFunc dom _ width _).trans
    (scalar hb i (Or.inr (hp.trans_eq ch.symm)) (dom.trans ⟨φ,φ.injective⟩))

/-- At length 2^30, a 222-bit power-of-two lower bound on the prime suffices
for the usual integer 128-bit list budget at all four radii and all widths. -/
theorem production_budget {p : ℕ} [Fact p.Prime] (hp : 2^222 ≤ p) (i : Fin 4)
    (dom : Fin (262144*4096) ↪ ZMod p) (width : ℕ) :
    let c := profiles i
    Code.Lambda (Code.interleavedCodeSet (κ := Fin width) (code dom (262144*c.k) : Set (Fin (262144*4096) → ZMod p)))
      (1-(c.A:ℝ)/4096) ≤ ((p/2^128:ℕ):ℕ∞) := by
  apply (all_width (by decide : 0<262144) i dom width).trans
  exact_mod_cast (Nat.le_div_iff_mul_le (by decide : 0<2^128)).mpr
    ((by fin_cases i <;> decide : (profiles i).listFactor*(262144*4096)^2*2^128 ≤ 2^222).trans hp)

end ProximityGap.SecondOrderAllWidthLists
#print axioms ProximityGap.SecondOrderAllWidthLists.all_width

#print axioms ProximityGap.SecondOrderAllWidthLists.production_budget
