/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSpikeBudgetRange
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Exact MCA radii for fields of size proportional to the block length

The apolar family inequality and the universal spike do not use the
multiplicative structure of the evaluation domain. They give a finite
integer criterion valid at every length, field size and dimension.
-/

set_option autoImplicit false
namespace ProximityGap.LinearFieldBudgetRadius
open Finset MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- Small-ball upper bound at an arbitrary Hamming step of an arbitrary domain. -/
theorem upper (x : Fin n ↪ F) {k e : ℕ} (hk : 1≤k) (hroom : k+2*e≤n)
    (hfit : k+e<n) (gap : n < (e+1)*(n-k+1-2*e)) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      ((e+1 : ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  classical
  apply epsMCA_le_of_badCount_le
  intro u
  let δ : ℝ≥0 := (e:ℝ≥0)/n
  let fam := canonicalBadScalarRichPointFamily x δ u hk
  change fam.G.card ≤ e+1
  let d := n-k-1
  have hn : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have ceil : ⌈(1-δ)*(Fintype.card (Fin n):ℝ≥0)⌉₊ = n-e := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ hn,
      ← Nat.cast_tsub,Nat.ceil_natCast]
  have h := ApolarMovingCount.count_mca_family (algebraMap F (AlgebraicClosure F))
    fam fam.G (Finset.Subset.rfl) (e:=e) (d:=d) (by dsimp [d];omega) (by dsimp [d];omega) hk
    (by rw [Fintype.card_fin];dsimp [d];omega) (by rw [ceil,Fintype.card_fin])
  rcases h with h|h
  · exact h
  · by_contra! larger
    apply gap.not_ge
    rw [Fintype.card_fin,show d+2-2*e = n-k+1-2*e by dsimp [d];omega] at h
    exact (Nat.mul_le_mul_right _ (by omega : e+1 ≤ fam.G.card-1)).trans h

/-- At e errors the spike attains at least e+1 bad labels on any injective domain. -/
theorem spike (x : Fin n ↪ F) {k e : ℕ} (hroom : e+1+k ≤ n) :
    ((e+1 : ℕ):ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) ≤
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) := by
  let pos : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
  rw [← BoundarySecurityBudget.rsCode_eq_code]
  exact SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode x k) (SpikeFloor.rsCode_noWeightLE x hroom)
    (by simp) (by omega) (by rw [Fintype.card_fin];omega)
    pos (pos.trans x) (b:=(1:F)) one_ne_zero

/-- An exact finite threshold for general security denominator Q. The first
bad error count is the integer budget B, including the case of a nonzero
remainder in the division of the field size by Q. -/
theorem exact_radius (x : Fin n ↪ F) {Q B k : ℕ} (hQ : 0<Q) (hk : 1≤k)
    (hB : B=Fintype.card F/Q) (hpos : 1≤B) (hroom : k+2*B≤n)
    (gap : n < B*(n-k+3-2*B)) :
    mcaDeltaStar (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (1/(Q:ℝ≥0∞)) =
      (B:ℝ≥0)/n := by
  have a := upper x (e:=B-1) hk (by omega) (by omega) (by
    rw [show B-1+1=B by omega,show n-k+1-2*(B-1) = n-k+3-2*B by omega]
    exact gap)
  have b := spike x (e:=B) (k:=k) (by omega)
  have posq : 0<Fintype.card F := Fintype.card_pos
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad _ _
    apply lt_of_lt_of_le _ b
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff posq hQ,← hB]
    omega
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good hpos (by omega : B≤n)
    apply a.trans
    rw [BoundarySecurityBudget.count_ratio_le_iff posq hQ,← hB]
    omega

end ProximityGap.LinearFieldBudgetRadius
#print axioms ProximityGap.LinearFieldBudgetRadius.exact_radius
#print axioms ProximityGap.LinearFieldBudgetRadius.upper
