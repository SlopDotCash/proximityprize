/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondOrderPrimeFieldCuts
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup

/-! # Exact second-order stage counting at the production length

The finite mixed-degree count retains the message dimension and an explicitly
chosen intermediate agreement threshold. At the BLS scalar prime its allowed
128-bit budget covers every prescribed length-2^30 domain at sixteenth rate.
-/
namespace ProximityGap.SecondOrderSharpProduction
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential Polynomial Finset
open PartitionOriginCertificate SecondOrderOriginBlocks SecondOrderBlockCounts
open scoped NNReal ENNReal

private theorem sharp_mono (r n k L A : ℕ) {v v' h h' : ℕ} (hv : v ≤ v') (hh : h ≤ h') :
    regularPowerBatchedAgreementSharpBound r n 1 k k L A v h ≤
      regularPowerBatchedAgreementSharpBound r n 1 k k L A v' h' := by
  have ha := dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
  have hl := dimensionSensitiveIncidenceProduct_nonneg n L k 1 r
  unfold regularPowerBatchedAgreementSharpBound regularPowerBatchedInitialMixedDegree
    regularPowerBatchedCutJetDegree regularPowerBatchedCutChallengeDegree
  gcongr

open Classical in
/-- Any degree-one certificate with height at most `H` gives a finite
base-field exceptional set when each possible stage fits the supplied
integer cap. The stage index and evaluation threshold may be chosen before
the received words. -/
theorem sharp_line_of_certificate {F : Type} [Field F] {n k A d v h H L S : ℕ}
    (dom : Fin n ↪ F) (f w : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate A k 1 v d h dom
      (fun i => powerBatchedCoordinate (ℓ := 1) fun j => (![f,w] : Fin 2 → Fin n → F) j i))
    (hd : d < k) (hkL : k ≤ L) (hLA : L ≤ A) (hh : h ≤ H)
    (hchar : ringChar F=0 ∨ max (k-1) v < ringChar F)
    (hcost : ∀ s : Fin (d+1), regularPowerBatchedAgreementSharpBound s.val n 1 k k L A v H ≤ S) :
    ∃ E : Finset F, E.card ≤ H+v*S ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet dom (fun i => f i+z*w i) P).card →
      HasExactCorrelatedPair dom f w (RingHom.id F) k z P := by
  classical
  let values : Fin 2 → Fin n → F := ![f,w]
  let ι := algebraMap F (AlgebraicClosure F)
  have hk : 0<k := by omega
  have hjet := hchar.imp_right (fun hh => (Nat.le_max_right _ _).trans_lt hh)
  have hK := hchar.imp_right (fun hh => (Nat.le_max_left _ _).trans_lt hh)
  obtain ⟨stages,terminal,hc,E,hcard,hgood⟩ :=
    cert.exists_exceptional_powerBatchedAgreement_sharp_of_exponent ι k L (2*k)
      (fun r _ => taylorExponentSufficient_two_mul r k) (by omega) hd le_rfl hkL hLA hjet
      (by intro r _ i hri hi
          have hn := natCast_choose_ne_zero_of_ringChar (F := F) (D := k-1) (s := r) hK (i-r) (by omega)
          simpa only [Nat.sub_add_cancel hri.le] using hn)
  obtain ⟨E',hE',good⟩ := uniformExactPowerAgreement_of_extension dom values ι k A E hgood
  have stages_le : stages.toFinset.card ≤ v :=
    (List.toFinset_card_le _).trans (hc.length_le.trans cert.jetTotalDegree_le)
  have bound : (E.card:ℚ) ≤ H+(v:ℚ)*S := calc
    _ ≤ _ := hcard
    _ ≤ (H:ℚ) + ∑ _ ∈ stages.toFinset, (S:ℚ) := by
      apply add_le_add (by exact_mod_cast hh)
      apply sum_le_sum
      intro stage hs
      exact (sharp_mono _ _ _ _ _ ((hc.jetTotalDegree_le_of_mem (List.mem_toFinset.mp hs)).trans
        cert.jetTotalDegree_le) hh).trans (hcost stage.2)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr stages_le) (show (0:ℚ) ≤ S by positivity))
  refine ⟨E',hE'.trans (by exact_mod_cast bound),?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) values z = fun i => f i + z*w i := by
    funext i
    simp [values,powerBatchedWord,Fin.sum_univ_two]
  exact exactCorrelatedPair_of_powerAgreement_one dom ![f,w] (RingHom.id F) z P
    (good z hz P hP (by rwa [hw]))

private abbrev n := 1073741824
private abbrev k := 67108864
private abbrev A := 233308160
private abbrev m := 20
private abbrev W := 17
private abbrev v := 69
private abbrev H := 2786
private abbrev L := 77413220
private abbrev stageCap := 2233263588724038498968437022129007560

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem counts : blockBudget m W v = 10432 ∧ sourceBudget (k-1) (m*A) W v = 11478667313970 := by
  rw [← SecondOrderPrimeFieldCuts.blockSum_eq (by decide) (by decide),
    SecondOrderPrimeFieldCuts.sourceBudget_eq (by decide)]
  decide

set_option maxRecDepth 100000 in
private theorem stage_bound (s : Fin 3) :
    regularPowerBatchedAgreementSharpBound s.val n 1 k k L A v H ≤ stageCap := by
  fin_cases s <;> norm_num [regularPowerBatchedAgreementSharpBound,regularPowerBatchedInitialMixedDegree,
    regularPowerBatchedCutJetDegree,regularPowerBatchedCutChallengeDegree,dimensionSensitiveIncidenceProduct,
    n,k,L,A,v,H,stageCap]

open Classical in
/-- At every base field passing the characteristic guard, every line at the
production dimension has a bounded exceptional set with exact recovery. -/
theorem exact_recovery {F : Type} [Field F] (dom : Fin n ↪ F) (u w : Fin n → F)
    (hchar : ringChar F=0 ∨ max (k-1) v < ringChar F) :
    ∃ E : Finset F, E.card ≤ H+v*stageCap ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet dom (fun x => u x+z*w x) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) k z P := by
  let D := k-1
  have hd : 0 < D := by decide
  have hv := jet_cap (D := D) (L := m*A) (W := W) (v := v) (by decide)
  have lo := source_card_lower (L := m*A) (W := W) (v := v) hd
  have hr := origin_rank (F := F) (m := m) hd hv
  rw [counts.1] at hr
  rw [counts.2] at lo
  obtain ⟨cert⟩ := certificate_of_origin_rank hd le_rfl (show k ≤ D+1 by decide) dom
    (fun i => powerBatchedCoordinate (ℓ := 1) fun j => (![u,w] : Fin 2 → Fin n → F) j i)
    (fun _ => powerBatchedCoordinate_natDegree_le _) hv hr
    ((by decide : n*10432 < 11478667313970).trans_le lo)
  apply sharp_line_of_certificate dom u w cert (by decide) (by decide) (by decide) _ hchar stage_bound
  apply (Nat.div_le_div_left (Nat.sub_le_sub_right lo _) (by decide)).trans
  decide

/-- On every 2^30-point domain over the BLS12-381 scalar field, the literal
sixteenth-rate sponsor MCA error at the closed radius 3206/4096 is 128-bit safe. -/
theorem bls_sixteenth (dom : Fin n ↪ ZMod BlsScalarSubgroup.P) :
    epsMCA (F := ZMod BlsScalarSubgroup.P) (A := ZMod BlsScalarSubgroup.P)
      (code dom k : Set (Fin n → ZMod BlsScalarSubgroup.P)) ((3206:ℝ≥0)/4096) ≤
        1/((2^128:ℕ):ℝ≥0∞) := by
  classical
  have hsmall : (3206:ℝ≥0)/4096 ≤ 1 := by apply NNReal.coe_le_coe.mp; norm_num
  have hth : (A:ℝ≥0) ≤ (1-((3206:ℝ≥0)/4096))*n := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_sub hsmall]
    norm_num
  apply (SecondOrderPrimeFieldCuts.eps_of_exact dom _ hth (fun u w => exact_recovery dom u w
    (Or.inr (by rw [ZMod.ringChar_zmod_n]; decide)))).trans
  rw [ZMod.card]
  exact (BoundarySecurityBudget.count_ratio_le_iff (by decide) (by decide)).mpr (by decide)

end ProximityGap.SecondOrderSharpProduction
#print axioms ProximityGap.SecondOrderSharpProduction.bls_sixteenth
