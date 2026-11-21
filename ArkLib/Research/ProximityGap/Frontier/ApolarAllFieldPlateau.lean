/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarMovingCount
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Research.ProximityGap.Frontier._MCAAdjacentFloorExactPin
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-! # The unique-decoding plateau in every finite field and on every domain

Below the first two-head Hamming step the extremal numerator is exactly the
number of errors plus one. At the first two-head step its lower bound doubles.
Only the length and the dimension enter these claims.
-/
namespace ArkLib.ProximityGap.Frontier.ApolarAllFieldPlateau
open Code _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [Nonempty I] [DecidableEq I]

private theorem preunique_fin {n k a e : ℕ} [NeZero n] (D : Fin n ↪ F)
    (hk : 2 ≤ k) (hlen : k+2*a=n) (hthird : n<3*a) (he : e<a) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (Fin n → F)) ((e : ℝ≥0)/n) =
      ((e+1 : ℕ) : ℝ≥0∞)/Fintype.card F := by
  classical
  have nonzero : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  apply le_antisymm
  · by_cases zero : e=0
    · subst e
      rw [← BoundarySecurityBudget.rsCode_eq_code]
      exact SpikeFloor.epsMCA_le_j_div_card (j:=1) (SpikeFloor.rsCode D k)
        (SpikeFloor.rsCode_noWeightLE D (by omega)) (by simp)
    apply epsMCA_le_of_badCount_le _ _ (e+1)
    intro u
    let δ : ℝ≥0 := (e:ℝ≥0)/n
    let fam := canonicalBadScalarRichPointFamily D δ u (by omega : 1 ≤ k)
    change fam.G.card ≤ e+1
    have limit := ApolarMovingCount.count_mca_family (algebraMap F (AlgebraicClosure F))
      fam fam.G Finset.Subset.rfl (e:=e) (d:=2*a-1) (by omega) (by omega) (by omega) (by rw [Fintype.card_fin];omega)
      (by dsimp only [δ]; rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ nonzero,← Nat.cast_tsub,Nat.ceil_natCast])
    rcases limit with cap | cap
    · exact cap
    rw [Fintype.card_fin] at cap
    by_contra! high
    let j := e+1
    have gap : n < j*(2*a+3-2*j) := by
      have bounds : 2 ≤ j ∧ j ≤ a := by dsimp [j];omega
      zify [show 2*j ≤ 2*a+3 by omega] at *
      nlinarith [mul_nonneg (show (0:ℤ) ≤ (j:ℤ)-2 by omega) (show (0:ℤ) ≤ (a:ℤ)-j by omega)]
    have hfactor : 2*a-1+2-2*e=2*a+3-2*j := by dsimp [j];omega
    rw [hfactor] at cap
    exact gap.not_ge ((Nat.mul_le_mul_right _ (by dsimp [j];omega : j≤fam.G.card-1)).trans cap)
  · rw [← BoundarySecurityBudget.rsCode_eq_code]
    let positions : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
    exact SpikeFloor.epsMCA_ge_j_div_card (j:=e+1) (SpikeFloor.rsCode D k)
      (SpikeFloor.rsCode_noWeightLE D (by omega))
      (by simp [Fintype.card_fin,div_mul_cancel₀ _ nonzero]) (by omega) (by rw [Fintype.card_fin];omega)
      positions (positions.trans D) (b:=(1:F)) one_ne_zero

/-- The spike is extremal on every grid step strictly below half the redundancy. -/
theorem preunique_mass (D : I ↪ F) {k a e : ℕ} (hk : 2 ≤ k)
    (hlen : k+2*a=Fintype.card I) (hthird : Fintype.card I<3*a) (he : e<a) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) ((e : ℝ≥0)/Fintype.card I) =
      ((e+1 : ℕ) : ℝ≥0∞)/Fintype.card F := by
  let eqv := Fintype.equivFin I
  let domain := eqv.symm.toEmbedding.trans D
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm domain D (fun _ => rfl)]
  exact preunique_fin domain hk hlen hthird he

/-- For every positive interleaving width and every positive reciprocal integer
tolerance, the exact first failure through the plateau is the smaller of the
budget and half the redundancy. The statement includes the zero budget. -/
theorem classification (D : I ↪ F) {k a B Q : ℕ} (hk : 2 ≤ k)
    (hlen : k+2*a=Fintype.card I) (hthird : Fintype.card I<3*a)
    (hQ : 0<Q) (hB : Fintype.card F/Q=B) (hu : B≤2*a+1) (m : ℕ) [NeZero m] :
    let C := (ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)
    let r : ℝ≥0 := ((min B a : ℕ) : ℝ≥0)/Fintype.card I
    mcaDeltaStar (F:=F) C (1/(Q : ℝ≥0∞))=r ∧ ∀ δ : ℝ≥0, epsMCA (F:=F) C δ ≤ 1/(Q : ℝ≥0∞) ↔ δ<r := by
  classical
  let C := (ReedSolomon.code D k : Set (I → F))
  let j := min B a
  let r : ℝ≥0 := (j:ℝ≥0)/Fintype.card I
  have ratio (l : ℕ) : ((l:ℝ≥0∞)/Fintype.card F ≤ 1/(Q:ℝ≥0∞)) ↔ l≤B := by
    rw [← hB]
    exact BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ
  have bad : 1/(Q : ℝ≥0∞) < epsMCA (F:=F) C r := by
    by_cases small : B<a
    · have cut := preunique_mass D hk hlen hthird small
      dsimp only [C,r,j]
      rw [min_eq_left small.le,cut]
      exact lt_of_not_ge (fun h => (by omega : ¬ B+1≤B) ((ratio _).1 h))
    · have cut := TwoHeadLinearBudget.errors D (k:=k) (e:=a) (by omega) (by omega) (by omega)
      dsimp only [C,r,j]
      rw [min_eq_right (by omega : a≤B)]
      apply lt_of_lt_of_le _ cut
      exact lt_of_not_ge (fun h => (by omega : ¬ 2*(a+1)≤B) ((ratio _).1 h))
  have radius : mcaDeltaStar (F:=F) C (1/(Q : ℝ≥0∞))=r := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ bad) (by simp [r,zero])
    have good : epsMCA (F:=F) C (((j-1:ℕ):ℝ≥0)/Fintype.card I) ≤ 1/(Q:ℝ≥0∞) := by
      have hja : j≤a := min_le_right ..
      have hjb : j≤B := min_le_left ..
      have h := preunique_mass D hk hlen hthird (by omega : j-1<a)
      exact h.le.trans ((ratio _).2 (by omega))
    let eqv := Fintype.equivFin I
    let domain := eqv.symm.toEmbedding.trans D
    have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm domain D (fun _ => rfl) k
    dsimp only [C]
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm domain D (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a:=j)
      (by omega) ((min_le_right ..).trans (by omega : a≤Fintype.card I))
    · rw [← hre]; exact good
    · rw [← hre]; exact bad
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨radius,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro safe
    by_contra! above
    exact bad.not_ge ((epsMCA_mono C above).trans safe)
  · intro below
    by_contra! unsafeAt
    have h := mcaDeltaStar_le_of_bad C (1/(Q:ℝ≥0∞)) unsafeAt
    rw [radius] at h
    exact below.not_ge h

#print axioms preunique_mass
#print axioms classification
end ArkLib.ProximityGap.Frontier.ApolarAllFieldPlateau
