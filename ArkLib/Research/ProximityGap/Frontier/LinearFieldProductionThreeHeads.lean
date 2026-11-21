/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeHeadDifferences
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicBudgetWindow

/-! # The production three-head probability in smaller prime fields

At length 2^30 and dimension 2^26, consecutive coefficients reduce the
sufficient prime-field size from a pair count above 2^60 to below 2^38.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.LinearFieldProductionThreeHeads
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger TerminalDomainSecurity PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

private theorem attack (dom : I ↪ ZMod p) (hn : Fintype.card I=n) {e : ℕ}
    (field : 223338305842≤p) (lo : 671088641≤e) (hi : e≤715827882) :
    ((3*(e+1):ℕ):ℝ≥0∞)/(p:ℝ≥0∞) ≤ epsMCA (F:=ZMod p)
      (ReedSolomon.code dom k : Set (I → ZMod p)) ((e:ℝ≥0)/n) := by
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
  have witness := PrimeHeadDifferences.grid_mass (t:=n-e) (m:=3) (k:=k) x ((e:ℝ≥0)/n)
    (by decide) (by decide) (by dsimp [n,k];omega) (Nat.sub_le ..) (by dsimp [n,k];omega)
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num [n]),← Nat.cast_tsub])
    (by dsimp [n,k];omega)
  rwa [show n-(n-e)=e by dsimp [n];omega] at witness

/-- The exact probability on all 44,739,241 grid points, at every positive width. -/
theorem exact_eps (dom : I ↪ ZMod p) (hn : Fintype.card I=n) {e : ℕ}
    (field : 223338305842≤p) (lo : 671088641≤e) (hi : e≤715827881)
    (width : ℕ) [NeZero width] :
    epsMCA (F:=ZMod p) ((ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)) ((e:ℝ≥0)/n) =
      ((3*(e+1):ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  rw [epsMCA_interleaved_eq]
  apply le_antisymm _ (attack dom hn field lo (by omega))
  simpa only [ZMod.card] using UniversalCubicBudgetWindow.eps_upper (p:=p) dom hn
    (.inl (by omega)) (by omega : 671088640≤e) hi

/-- For every security denominator placing the crossing on this interval,
the exact all-width operational threshold is the rounded third of the budget. -/
theorem classification (dom : I ↪ ZMod p) (hn : Fintype.card I=n) {Q j : ℕ}
    (field : 223338305842≤p) (hQ : 0<Q) (index : j=p/Q/3)
    (lo : 671088641≤j) (hi : j≤715827882) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)
    let ε := 1/(Q:ℝ≥0∞)
    let b := (j:ℝ≥0)/n
    mcaDeltaStar (F:=ZMod p) C ε=b ∧ ∀ δ, epsMCA (F:=ZMod p) C δ≤ε ↔ δ<b := by
  dsimp only
  let C := (ReedSolomon.code dom k : Set (I → ZMod p)) ^⋈ (Fin width)
  have pos : 0<j := by omega
  have good : epsMCA (F:=ZMod p) C (predecessorRadius n j) ≤ 1/(Q:ℝ≥0∞) := by
    unfold C predecessorRadius
    rw [epsMCA_interleaved_eq]
    apply (UniversalCubicBudgetWindow.eps_upper (p:=p) dom hn (.inl (by omega))
      (by omega : 671088640≤j-1) (by omega)).trans
    rw [ZMod.card,BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos hQ,
      Nat.sub_add_cancel pos,index]
    omega
  have bad : 1/(Q:ℝ≥0∞)<epsMCA (F:=ZMod p) C ((j:ℝ≥0)/n) := by
    unfold C
    rw [epsMCA_interleaved_eq]
    apply lt_of_lt_of_le _ (attack dom hn field lo hi)
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos hQ,index]
    omega
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  have reindex := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl) k
  have result : mcaDeltaStar (F:=ZMod p) C (1/(Q:ℝ≥0∞)) = (j:ℝ≥0)/n := by
    unfold C
    rw [mcaDeltaStar_interleaved_eq,
      MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq eqv.symm x dom (fun _ => rfl)]
    apply MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      pos (show j≤n by dsimp [n];omega)
    · rw [←reindex]
      simpa only [C,epsMCA_interleaved_eq,PrizeShapeRateHalfBracket.predecessorRadius,
        MCAAdjacentFloorExactPin.predecessorRadius,MCAAdjacentFloorExactPin.latticeRadius] using good
    · rw [←reindex]
      simpa only [C,epsMCA_interleaved_eq,MCAAdjacentFloorExactPin.latticeRadius] using bad
  refine ⟨result,fun δ => ⟨fun h => ?_,fun h => ?_⟩⟩
  · by_contra! hb
    exact bad.not_ge ((epsMCA_mono C hb).trans h)
  · by_contra! fail
    exact h.not_ge (result ▸ mcaDeltaStar_le_of_bad C _ fail)

end ArkLib.ProximityGap.Frontier.LinearFieldProductionThreeHeads
#print axioms ArkLib.ProximityGap.Frontier.LinearFieldProductionThreeHeads.exact_eps
#print axioms ArkLib.ProximityGap.Frontier.LinearFieldProductionThreeHeads.classification
