/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothQuarterTwoHeadWindow

/-! # The quarter-rate probability at real radii and the boundary at real tolerances -/
namespace ArkLib.ProximityGap.Frontier.QuarterRateToleranceCurve
open Code _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger ProximityPrize
open scoped NNReal ENNReal
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

omit [DecidableEq F] in
/-- Convert any nonnegative real tolerance to its exact integer scalar budget. -/
private theorem fits (ε : ℝ≥0) (l : ℕ) :
    (l : ℝ≥0∞)/Fintype.card F ≤ ε ↔ l ≤ RankReview.budget F ε := by
  rw [ENNReal.div_le_iff (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)]
  change _ ↔ l ≤ ⌊ε * (Fintype.card F : ℝ≥0)⌋₊
  rw [Nat.le_floor_iff (by positivity)]
  norm_cast

/-- The worst probability at every real radius strictly below the successor of
the saturated step, at every positive interleaving width. -/
theorem probability (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I=1073741824)
    (hq : Fintype.card F<2^256) (m : ℕ) [NeZero m] (δ : ℝ≥0) (hr : δ < 447392428/1073741824) :
    let e := ⌊δ*1073741824⌋₊
    epsMCA (F:=F) ((ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m)) δ =
      ((if e<402653184 then e+1 else 2*(e+1) : ℕ) : ℝ≥0∞)/Fintype.card F := by
  let e := ⌊δ*1073741824⌋₊
  have ha : e < 447392428 := (Nat.floor_lt (by norm_num)).mpr ((lt_div_iff₀ (by norm_num)).mp hr)
  have step : ⌊δ * (Fintype.card I : ℝ≥0)⌋₊ =
      ⌊((e : ℝ≥0)/1073741824)*(Fintype.card I : ℝ≥0)⌋₊ := by
    rw [hn]
    change e = ⌊((e : ℝ≥0)/1073741824)*1073741824⌋₊
    rw [div_mul_cancel₀ _ (by norm_num),Nat.floor_natCast]
  dsimp only
  rw [epsMCA_interleaved_eq,epsMCA_eq_of_floor_eq (F:=F) (A:=F) _ step]
  have h := SmoothQuarterTwoHeadWindow.full_grid_mass D hn hq (e:=e) (by omega) m
  rwa [epsMCA_interleaved_eq] at h

/-- For every real tolerance with budget in the complete window, every real
radius is classified and the support-rank answer is the same explicit integer. -/
theorem classification (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I=1073741824)
    (hq : Fintype.card F<2^256) (ε : ℝ≥0) (hu : RankReview.budget F ε ≤ 894784857) (m : ℕ) [NeZero m] :
    let B := RankReview.budget F ε
    let j := min B (max 402653184 (B/2))
    let r : ℝ≥0 := (j:ℝ≥0)/1073741824
    let C := (ReedSolomon.code D 268435456 : Set (I → F)) ^⋈ (Fin m)
    mcaDeltaStar (F:=F) C (ε:ℝ≥0∞) = r ∧
      (∀ δ : ℝ≥0, epsMCA (F:=F) C δ ≤ (ε:ℝ≥0∞) ↔ δ<r) ∧
      (RankReview.mcaAnswer D ε 268435456).map Fin.val = some j := by
  classical
  let C := (ReedSolomon.code D 268435456 : Set (I → F))
  let B := RankReview.budget F ε
  let j := min B (max 402653184 (B/2))
  let r : ℝ≥0 := (j:ℝ≥0)/1073741824
  have inside : j < Fintype.card I := by change B≤894784857 at hu; dsimp [j]; omega
  have grid (e : ℕ) (h : e≤447392427) := SmoothQuarterTwoHeadWindow.full_grid_mass D hn hq (e:=e) h 1
  simp only [epsMCA_interleaved_eq] at grid
  have bad : (ε:ℝ≥0∞) < epsMCA (F:=F) C r := by
    dsimp only [r,C]
    by_cases last : 447392427 < j
    · have cut := TwoHeadLinearBudget.errors D (k:=268435456) (e:=j) (by dsimp [j];change B≤894784857 at hu;omega)
        (by omega) (by dsimp [j];change B≤894784857 at hu;omega)
      rw [hn] at cut
      apply lt_of_lt_of_le _ cut
      apply lt_of_not_ge
      rw [fits]
      change ¬2*(j+1)≤B
      dsimp [j] at *
      omega
    · rw [grid j (by omega)]
      apply lt_of_not_ge
      rw [fits]
      change ¬ (if j<402653184 then j+1 else 2*(j+1))≤B
      dsimp [j]
      split <;> omega
  have radius : mcaDeltaStar (F:=F) C (ε:ℝ≥0∞) = r := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ bad) (by simp [r,zero])
    have prev : j-1≤447392427 := by change B≤894784857 at hu; dsimp [j];omega
    have good : epsMCA (F:=F) C (((j-1:ℕ):ℝ≥0)/1073741824) ≤ (ε:ℝ≥0∞) := by
      rw [show C = _ from rfl,grid _ prev,fits]
      change (if j-1<402653184 then j-1+1 else 2*(j-1+1)) ≤ B
      dsimp [j] at *
      split <;> omega
    let eqv := Fintype.equivFinOfCardEq hn
    let domain := eqv.symm.toEmbedding.trans D
    have hre := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm domain D (fun _ => rfl) 268435456
    dsimp only [C]
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm domain D (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad (a:=j) (by omega) (by omega)
    · rw [← hre]; exact good
    · rw [← hre]; exact bad
  let ix : Fin (Fintype.card I+1) := ⟨j,by omega⟩
  have rank := SecondPrimeRankReview.rankAnswer_of_interior_supremum D ε 268435456 ix inside
    (by change _ = (j : ℝ≥0)/Fintype.card I; rw [hn];exact radius)
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨radius,?_,congrArg (Option.map Fin.val) rank⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  exact SecondPrimeRankReview.safe_iff_of_interior_supremum C ε r
    (by dsimp only [r]; rw [div_lt_one (by norm_num)];exact_mod_cast hn ▸ inside) radius δ

#print axioms probability
#print axioms classification
end ArkLib.ProximityGap.Frontier.QuarterRateToleranceCurve
