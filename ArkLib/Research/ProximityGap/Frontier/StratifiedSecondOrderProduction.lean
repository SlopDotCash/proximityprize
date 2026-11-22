/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondOrderSharpProduction

/-! # Charging each stage at its actual differential degree

Total jet degree strictly decreases along a separant chain. Charging each
degree once gives a sum of cubes in the order-two mixed-degree bound and
sharpens the BLS scalar-field endpoints for three sponsor rates.
-/
namespace ProximityGap.StratifiedSecondOrderProduction
open ReedSolomon ReedSolomon.HiddenDerivative PolynomialDifferential Polynomial Finset
open PartitionOriginCertificate SecondOrderOriginBlocks SecondOrderSharpProduction
open scoped NNReal ENNReal

open Classical in
/-- A separant chain can charge each total jet degree at most once. -/
theorem sum_degree_le {R : Type*} [CommRing R] {d : ℕ} [DecidableEq (SeparantStage R d)] {Q T : DifferentialPolynomial R d}
    {stages : List (SeparantStage R d)} (hc : SeparantChain Q stages T)
    (f : ℕ → ℚ) (hf : ∀ t, 0≤f t) :
    (∑ s ∈ stages.toFinset, f (jetTotalDegree s.1)) ≤ ∑ t ∈ range (jetTotalDegree Q+1), f t := by
  classical
  induction hc with
  | terminal => simpa using sum_nonneg (fun t (_ : t ∈ range (jetTotalDegree _ + 1)) => hf t)
  | @active Q tail term j hne hhigh next ih =>
    have lt := jetTotalDegree_separant_lt (isHighestActiveJet_of_highestActiveJet_eq_some hhigh).1
    have hnot : (Q,j) ∉ tail.toFinset := by
      intro hm
      have he := next.jetTotalDegree_le_of_mem (List.mem_toFinset.mp hm)
      exact (not_le.mpr lt) he
    rw [List.toFinset_cons,sum_insert hnot,sum_range_succ,add_comm]
    apply add_le_add _ le_rfl
    exact ih.trans (sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun t _ _ => hf t))

/-- Coefficient of the order-`r` degree power, at Taylor exponent `2k`. -/
def stageUnit (r n k L A H : ℕ) : ℚ :=
  let τ := 2*k
  let b := 1+τ*H
  (((H*τ^(r+1)+(r+1)*b*τ^r:ℕ):ℚ) * (((n-L+1:ℕ):ℚ)/(A-L+1:ℕ))) *
    dimensionSensitiveIncidenceProduct n A k 1 r +
  (((n-L)*τ^r:ℕ):ℚ) * dimensionSensitiveIncidenceProduct n L k 1 r

private theorem stage_le_unit (r n k L A H t h : ℕ) (hk : 0<k) (ht : 0<t) (hh : h≤H) :
    regularPowerBatchedAgreementSharpBound r n 1 k k L A t h ≤ stageUnit r n k L A H * (t:ℚ)^(r+1) := by
  let τ := 2*k
  have ha := dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
  have hl := dimensionSensitiveIncidenceProduct_nonneg n L k 1 r
  have jet : 1+τ*(t-1) ≤ τ*t := by
    cases t with
    | zero => omega
    | succ t => simp only [Nat.succ_sub_one,Nat.mul_succ]; dsimp [τ]; omega
  have mixed : h*(1+τ*(t-1))^(r+1)+(r+1)*t*(1+τ*h)*(1+τ*(t-1))^r ≤
      (H*τ^(r+1)+(r+1)*(1+τ*H)*τ^r)*t^(r+1) := calc
    _ ≤ H*(τ*t)^(r+1)+(r+1)*t*(1+τ*H)*(τ*t)^r := by gcongr
    _ = _ := by rw [mul_pow,mul_pow]; ring
  have last : (n-L)*t*(1+τ*(t-1))^r ≤ ((n-L)*τ^r)*t^(r+1) := calc
    _ ≤ (n-L)*t*(τ*t)^r := by gcongr
    _ = _ := by rw [mul_pow]; ring
  unfold regularPowerBatchedAgreementSharpBound regularPowerBatchedInitialMixedDegree
    regularPowerBatchedCutJetDegree regularPowerBatchedCutChallengeDegree
  simp only [one_mul]
  calc
    _ ≤ (((H*τ^(r+1)+(r+1)*(1+τ*H)*τ^r)*t^(r+1):ℕ):ℚ) *
      (((n-L+1:ℕ):ℚ)/(A-L+1:ℕ))*dimensionSensitiveIncidenceProduct n A k 1 r +
      ((((n-L)*τ^r)*t^(r+1):ℕ):ℚ)*dimensionSensitiveIncidenceProduct n L k 1 r := by
        rw [← Nat.cast_pow,← Nat.cast_mul]
        gcongr
        exact_mod_cast last
    _ = _ := by simp only [stageUnit,Nat.cast_mul,Nat.cast_pow,τ]; ring

private theorem cube_bound (n k L A H C t h : ℕ) (s : Fin 3) (hk : 0<k)
    (ht : 0<t) (hh : h≤H) (hs : stageUnit s.val n k L A H ≤ C) :
    regularPowerBatchedAgreementSharpBound s.val n 1 k k L A t h ≤ (C:ℚ)*(t:ℚ)^3 := by
  have hx : (1:ℚ) ≤ t := by exact_mod_cast ht
  have hj : s.val+1 ≤ 3 := s.isLt
  exact (stage_le_unit s.val n k L A H t h hk ht hh).trans
    (mul_le_mul hs (pow_le_pow_right₀ hx hj) (by positivity) (Nat.cast_nonneg _))

private theorem cast_budget {H C v cap : ℕ}
    (hb : H + C*(∑ t ∈ range (v+1), t^3) ≤ cap) :
    (H:ℚ) + ∑ t ∈ range (v+1), (C:ℚ)*(t:ℚ)^3 ≤ cap := by
  rw [← mul_sum]
  exact_mod_cast hb

set_option maxHeartbeats 2000000 in
open Classical in
/-- A second-order line certificate gives a base-field exceptional count under
the three explicit mixed-degree unit bounds and a finite sum of cubes. -/
theorem exact_of_cubics {F : Type} [Field F] {n k A v h H L C cap : ℕ}
    (dom : Fin n ↪ F) (u w : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate A k 1 v 2 h dom
      (fun i => powerBatchedCoordinate (ℓ := 1) fun j => (![u,w] : Fin 2 → Fin n → F) j i))
    (hk : 2 < k) (hkL : k≤L) (hLA : L≤A) (hh : h≤H)
    (hchar : ringChar F=0 ∨ max (k-1) v < ringChar F)
    (hs : ∀ r : Fin 3, stageUnit r.val n k L A H ≤ C)
    (hbudget : H + C*(∑ t ∈ range (v+1), t^3) ≤ cap) :
    ∃ E : Finset F, E.card ≤ cap ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet dom (fun i => u i+z*w i) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) k z P := by
  classical
  apply sharp_line_of_stage_budget dom u w cert hk hkL hLA hchar
  intro stages term hc
  let F3 (t : ℕ) : ℚ := (C:ℚ)*t^3
  have hf (t : ℕ) : 0≤F3 t := by dsimp [F3]; positivity
  have hsum := sum_degree_le hc F3 hf
  have hfinal : ∑ t ∈ range (jetTotalDegree cert.Q+1), F3 t ≤ ∑ t ∈ range (v+1), F3 t :=
    sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ cert.jetTotalDegree_le)) (fun t _ _ => hf t)
  calc
    _ ≤ (H:ℚ) + ∑ s ∈ stages.toFinset, F3 (jetTotalDegree s.1) := by
        apply add_le_add (Nat.cast_le.mpr hh)
        apply sum_le_sum
        intro s hst
        have hact := (isHighestActiveJet_of_highestActiveJet_eq_some
          (hc.highestActiveJet_eq_of_mem (List.mem_toFinset.mp hst))).1
        have ht : 0 < jetTotalDegree s.1 := hact.trans_le (jetDegree_le_total _ _)
        exact cube_bound n k L A H C (jetTotalDegree s.1) h s.2 (by omega) ht hh (hs s.2)
    _ ≤ (H:ℚ) + ∑ t ∈ range (v+1), F3 t := add_le_add le_rfl (hsum.trans hfinal)
    _ ≤ _ := cast_budget hbudget

private abbrev n := 1073741824

structure Profile where
  k : ℕ
  A : ℕ
  m : ℕ
  W : ℕ
  v : ℕ
  H : ℕ
  L : ℕ
  r : ℕ
  N : ℕ
  stageCap : ℕ
  errorsPer4096 : ℕ
  deriving DecidableEq

/-- Production parameters in quarter, eighth, and sixteenth rate order. -/
def profiles : Fin 3 → Profile
  | 0 => ⟨268435456,503316480,25,15,46,4619,277595815,14274,15479196428160,
    131867474288427096598998387355817,2176⟩
  | 1 => ⟨134217728,339738624,26,19,65,4164,143877210,21972,23960507090025,
    33491491052962906402121734728001,2800⟩
  | 2 => ⟨67108864,230686720,24,21,82,5071,75451334,21426,23377977195342,
    13306541040299928649223197084567,3216⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem counts (i : Fin 3) : let c := profiles i
    blockBudget c.m c.W c.v = c.r ∧ sourceBudget (c.k-1) (c.m*c.A) c.W c.v = c.N := by
  dsimp only
  rw [← SecondOrderPrimeFieldCuts.blockSum_eq (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    SecondOrderPrimeFieldCuts.sourceBudget_eq (by fin_cases i <;> decide)]
  fin_cases i <;> decide

private theorem unit_bounds (i : Fin 3) (s : Fin 3) : let c := profiles i
    stageUnit s.val n c.k c.L c.A c.H ≤ c.stageCap := by
  fin_cases i <;> fin_cases s <;> norm_num [profiles,stageUnit,dimensionSensitiveIncidenceProduct,n]

set_option maxRecDepth 10000 in
private theorem total_cap (i : Fin 3) : let c := profiles i
    c.H + c.stageCap * (∑ t ∈ range (c.v+1), t^3) ≤ BlsScalarSubgroup.P/2^128 := by
  fin_cases i <;> decide

open Classical in
/-- Three sharp production thresholds on every field satisfying the
characteristic guard, with a common integer cap matching the BLS budget. -/
theorem exact_recovery {F : Type} [Field F] (i : Fin 3) (dom : Fin n ↪ F) (u w : Fin n → F)
    (hchar : ringChar F=0 ∨ max ((profiles i).k-1) (profiles i).v < ringChar F) :
    let c := profiles i
    ∃ E : Finset F, E.card ≤ BlsScalarSubgroup.P/2^128 ∧ ∀ z ∉ E, ∀ P : F[X], P.degree < c.k →
      c.A ≤ (polynomialAgreementSet dom (fun x => u x+z*w x) P).card →
      HasExactCorrelatedPair dom u w (RingHom.id F) c.k z P := by
  let c := profiles i
  have hd : 0 < c.k-1 := by fin_cases i <;> decide
  have hc : c.m*c.A ≤ (c.k-1)*(c.v+1) := by fin_cases i <;> decide
  have hv := jet_cap (W := c.W) hc
  have lo := source_card_lower (L := c.m*c.A) (W := c.W) (v := c.v) hd
  have hr := origin_rank (F := F) (m := c.m) hd hv
  rw [(counts i).1] at hr
  rw [(counts i).2] at lo
  have surplus : n*c.r < c.N := by fin_cases i <;> decide
  obtain ⟨cert⟩ := certificate_of_origin_rank hd le_rfl (show c.k ≤ c.k-1+1 by omega) dom
    (fun i => powerBatchedCoordinate (ℓ := 1) fun j => (![u,w] : Fin 2 → Fin n → F) j i)
    (fun _ => powerBatchedCoordinate_natDegree_le _) hv hr (surplus.trans_le lo)
  apply exact_of_cubics dom u w cert (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) _ hchar (unit_bounds i) (total_cap i)
  apply (Nat.div_le_div_left (Nat.sub_le_sub_right lo _) (Nat.sub_pos_of_lt surplus)).trans
  fin_cases i <;> decide

/-- Worst-pair closed radii of 2176, 2800, and 3216 units per 4096 on every
production-length BLS domain at the three respective rates. -/
theorem bls_three_rates (i : Fin 3) (dom : Fin n ↪ ZMod BlsScalarSubgroup.P) :
    let c := profiles i
    epsMCA (F := ZMod BlsScalarSubgroup.P) (A := ZMod BlsScalarSubgroup.P)
      (code dom c.k : Set (Fin n → ZMod BlsScalarSubgroup.P)) ((c.errorsPer4096:ℝ≥0)/4096) ≤
        1/((2^128:ℕ):ℝ≥0∞) := by
  classical
  let c := profiles i
  have hsmall : (c.errorsPer4096:ℝ≥0)/4096 ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    fin_cases i <;> norm_num [c,profiles]
  have hth : (c.A:ℝ≥0) ≤ (1-((c.errorsPer4096:ℝ≥0)/4096))*n := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul,NNReal.coe_sub hsmall]
    fin_cases i <;> norm_num [c,profiles,n]
  apply (SecondOrderPrimeFieldCuts.eps_of_exact dom _ hth (fun u w => exact_recovery i dom u w
    (Or.inr (by rw [ZMod.ringChar_zmod_n]; fin_cases i <;> decide)))).trans
  rw [ZMod.card]
  exact (BoundarySecurityBudget.count_ratio_le_iff (by decide) (by decide)).mpr le_rfl

end ProximityGap.StratifiedSecondOrderProduction
#print axioms ProximityGap.StratifiedSecondOrderProduction.exact_of_cubics

#print axioms ProximityGap.StratifiedSecondOrderProduction.bls_three_rates
