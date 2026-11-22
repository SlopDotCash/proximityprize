/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondOrderPrimeFieldCuts
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237

/-! # All four prize rates from scaled second-order interpolation

Scale the coarse degree with the message dimension. Each admissible jet
partition then has an integer multiple of the original horizontal width.
Consequently dimension and stacked rank scale together while the height
and normalized agreement slack stay fixed.
-/
namespace ProximityGap.ScaledSecondOrderPrimeCuts
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential Polynomial Finset
open PartitionOriginCertificate SecondOrderOriginBlocks SecondOrderBlockCounts
open scoped NNReal ENNReal

structure Profile where
  k : ℕ
  A : ℕ
  m : ℕ
  W : ℕ
  v : ℕ
  H : ℕ
  r : ℕ
  N : ℕ
  coefficient : ℕ
  deriving DecidableEq

/-- Half, quarter, eighth, and sixteenth rates at reference length 4096. -/
def profiles : Fin 4 → Profile
  | 0 => ⟨2048,2815,58,25,79,25551,209400,860354222,20007104463588681⟩
  | 1 => ⟨1024,1893,51,31,94,15936,213977,881619592,17198307386709643⟩
  | 2 => ⟨512,1279,40,30,99,10341,116314,480983040,19969708005140362⟩
  | 3 => ⟨256,875,28,25,95,6080,39404,163920484,18940036421599633⟩

/-- The source dimensional lower bound scales exactly. -/
theorem source_scaled (b D L W v : ℕ) :
    sourceBudget (b*D) (b*L) W v = b*sourceBudget D L W v := by
  rw [sourceBudget,sourceBudget,Finset.mul_sum]
  apply sum_congr rfl
  intro t _
  rw [Nat.mul_assoc b D t,← Nat.mul_sub]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
private theorem counts (i : Fin 4) : let c := profiles i
    blockBudget c.m c.W c.v = c.r ∧ sourceBudget c.k (c.m*c.A) c.W c.v = c.N := by
  dsimp only
  rw [←SecondOrderPrimeFieldCuts.blockSum_eq (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    SecondOrderPrimeFieldCuts.sourceBudget_eq (by fin_cases i <;> decide)]
  fin_cases i <;> decide

noncomputable def gap (c : Profile) : ℝ := ((c.A-c.k:ℕ):ℝ)/4096

private theorem field_charge (i : Fin 4) : let c := profiles i
    polynomialCurveProductAgreementConstant (gap c) c.v c.H 2 ≤ c.coefficient := by
  fin_cases i <;> norm_num [profiles,gap,polynomialCurveProductAgreementConstant]

open Classical in
/-- At every positive multiple of the reference length, all received pairs have
the same height bound and at most the explicit cubic number of bad scalars. -/
theorem exact_recovery {F : Type} [Field F] (i : Fin 4) {b : ℕ} (hb : 0<b)
    (dom : Fin (b*4096) ↪ F) (u w : Fin (b*4096) → F)
    (hchar : ringChar F = 0 ∨ max (b*(profiles i).k-1) (profiles i).v < ringChar F) :
    let c := profiles i
    ∃ E : Finset F, E.card ≤ c.coefficient*(b*4096)^3 ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < b*c.k →
      b*c.A ≤ (polynomialAgreementSet dom (fun x => u x+z*w x) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) (b*c.k) z P := by
  let c := profiles i
  have hk : 0 < c.k := by fin_cases i <;> decide
  have hcut : c.m*c.A ≤ c.k*(c.v+1) := by fin_cases i <;> decide
  have hcut' : b*(c.m*c.A) ≤ b*c.k*(c.v+1) := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left b hcut
  have hD := Nat.mul_pos hb hk
  have hv := jet_cap (W := c.W) hcut'
  have rank := origin_rank (F := F) (m := c.m) hD hv
  rw [(counts i).1] at rank
  have lower := source_card_lower (L := b*(c.m*c.A)) (W := c.W) (v := c.v) hD
  rw [source_scaled,(counts i).2] at lower
  have surplus : 4096*c.r < c.N := by fin_cases i <;> decide
  have scaledSurplus : b*4096*c.r < b*c.N := by simpa [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_left surplus hb
  have ht : 4096*c.r*c.v/(c.N-4096*c.r) ≤ c.H := by fin_cases i <;> decide
  have hH : b*4096*c.r*c.v/((partitionSupportExponents (b*c.k) 2 c.W (b*(c.m*c.A):ℕ) hD).card-b*4096*c.r) ≤ c.H := calc
    _ ≤ b*4096*c.r*c.v / (b*c.N-b*4096*c.r) :=
      Nat.div_le_div_left (Nat.sub_le_sub_right lower _) (Nat.sub_pos_of_lt scaledSurplus)
    _ = (b*(4096*c.r*c.v))/(b*(c.N-4096*c.r)) := by rw [Nat.mul_sub]; simp only [Nat.mul_assoc]
    _ = _ := Nat.mul_div_mul_left _ _ hb
    _ ≤ _ := ht
  have hn : b*c.k≤b*4096 := Nat.mul_le_mul_left _ (by fin_cases i <;> decide)
  have hAn : b*c.A≤b*4096 := Nat.mul_le_mul_left _ (by fin_cases i <;> decide)
  have hdk : 2 < b*c.k := calc 2 < c.k := by fin_cases i <;> decide
                                       _ ≤ _ := by nlinarith
  have hgap : (b*c.k:ℕ) + gap c*(b*4096:ℕ) ≤ (b*c.A:ℕ) := by
    have hg : (c.k:ℝ)+gap c*4096 = c.A := by fin_cases i <;> norm_num [c,profiles,gap]
    push_cast
    nlinarith [congrArg (fun x : ℝ => (b:ℝ)*x) hg]
  obtain ⟨E,he,good⟩ := exact_line_of_origin_rank hD
    (show ((b*(c.m*c.A):ℕ):ℝ)≤(c.m*(b*c.A):ℕ) by exact_mod_cast (show b*(c.m*c.A) ≤ c.m*(b*c.A) by rw [Nat.mul_left_comm]))
    (Nat.le_succ _) hv rank (scaledSurplus.trans_le lower) hH
    (by fin_cases i <;> decide) hD hdk hn hAn (show 0<gap c by fin_cases i <;> norm_num [c,profiles,gap])
    hgap hchar dom u w
  refine ⟨E, ?_, good⟩
  exact_mod_cast he.trans (mul_le_mul_of_nonneg_right (field_charge i) (by positivity))

/-- For each sponsor rate, the displayed profile gives the literal all-domain
128-bit endpoint whenever its cubic field requirement fits. -/
theorem eps_bound {p b : ℕ} [Fact p.Prime] (hb : 0<b) (i : Fin 4)
    (hp : 2^128*(profiles i).coefficient*(b*4096)^3 ≤ p) (dom : Fin (b*4096) ↪ ZMod p) :
    let c := profiles i
    epsMCA (F := ZMod p) (A := ZMod p) (code dom (b*c.k) : Set (Fin (b*4096) → ZMod p))
      (((4096-c.A:ℕ):ℝ≥0)/4096) ≤ 1/((2^128:ℕ):ℝ≥0∞) := by
  classical
  let c := profiles i
  letI : Nonempty (Fin (b*4096)) := ⟨⟨0,by omega⟩⟩
  let δ : ℝ≥0 := ((4096-c.A:ℕ):ℝ≥0)/4096
  have hδ1 : δ ≤ 1 := by apply NNReal.coe_le_coe.mp; fin_cases i <;> norm_num [c,δ,profiles]
  have hδ : ((b*c.A:ℕ):ℝ≥0) ≤ (1-δ)*(b*4096:ℕ) := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_sub hδ1]
    fin_cases i <;> norm_num [c,δ,profiles] <;> linarith
  have hchar : max (b*c.k-1) c.v < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]
    have hc : 1 ≤ 2^128*c.coefficient := by fin_cases i <;> decide
    have hz : b*4096 ≤ 2^128*c.coefficient*(b*4096)^3 :=
      (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans
        (by simpa only [one_mul] using Nat.mul_le_mul_right ((b*4096)^3) hc)
    have h₁ : c.k ≤ 4096 := by fin_cases i <;> decide
    have h₂ : c.v < 4096 := by fin_cases i <;> decide
    have hn := Nat.mul_le_mul_left b h₁
    have htotal : b*4096 ≤ p := hz.trans hp
    omega
  apply (SecondOrderPrimeFieldCuts.eps_of_exact dom δ hδ (fun u w => exact_recovery i hb dom u w (Or.inr hchar))).trans
  rw [ZMod.card]
  apply (BoundarySecurityBudget.count_ratio_le_iff (Fact.out : p.Prime).pos (by decide)).mpr
  apply (Nat.le_div_iff_mul_le (by decide : 0<2^128)).mpr
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp

open ArkLib.ProximityGap.Frontier
local instance : Fact DyadicLogWitness237.P.Prime := ⟨DyadicLogWitness237.prime⟩

/-- At the named 237-bit prime the same four closed endpoints cover every
positive multiple of 4096 through length 262144. -/
theorem witness_field {b : ℕ} (hb : 0 < b) (hlen : b ≤ 64) (i : Fin 4)
    (dom : Fin (b*4096) ↪ ZMod DyadicLogWitness237.P) :
    let c := profiles i
    epsMCA (F := ZMod DyadicLogWitness237.P) (A := ZMod DyadicLogWitness237.P)
      (code dom (b*c.k) : Set (Fin (b*4096) → ZMod DyadicLogWitness237.P))
      (((4096-c.A:ℕ):ℝ≥0)/4096) ≤ 1/((2^128:ℕ):ℝ≥0∞) := by
  apply eps_bound hb i _ dom
  calc 2^128*(profiles i).coefficient*(b*4096)^3
       ≤ 2^128*(profiles i).coefficient*(64*4096)^3 := by gcongr
     _ ≤ DyadicLogWitness237.P := by fin_cases i <;> decide

end ProximityGap.ScaledSecondOrderPrimeCuts
#print axioms ProximityGap.ScaledSecondOrderPrimeCuts.eps_bound

#print axioms ProximityGap.ScaledSecondOrderPrimeCuts.witness_field
