/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ArbitraryDomainHeadMass
import ArkLib.Research.ProximityGap.Frontier.GeneralManyLineSafety

/-! # A finite many-head threshold on every evaluation domain

The field-size test permits fields of linear size when dimension grows
proportionally with length. It bounds the degree spent on collision sites.
-/

set_option autoImplicit false
namespace ProximityGap.ArbitraryDomainHeadThreshold
open MCAThresholdLedger ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A finite cubic and core-geometry certificate on the predecessor and a
strict failure supplied by any construction determine the complete good interval. -/
theorem exact_threshold_of_bad {n k m Q j L : ℕ} [NeZero n] (x : Fin n ↪ F)
    (Qpos : 0 < Q) (heads : 1 ≤ m) (index : j=Fintype.card F/Q/m) (positive : 0 < j)
    (inside : j≤n) (degree : 2≤k) (agree : k<n-j) (scale : 2≤L)
    (moment : (j+1)*k*n^2+(L+2)*n^3 < (j+1)*(n-j+1)^3)
    (geometry : (n+(m.choose 2+m)*k)*L+m*n < (m+1)*(n-j+1)*L)
    (bad : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((j:ℝ≥0)/n)) :
    let C := (ReedSolomon.code x k : Set (Fin n → F))
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=F) C ε = bound ∧ ∀ δ, epsMCA (F:=F) C δ ≤ ε ↔ δ < bound := by
  dsimp only
  have nz : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have grid (e : ℕ) (he : e≤n) : (1-(e:ℝ≥0)/n)*(n:ℝ≥0) = ((n-e:ℕ):ℝ≥0) := by
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ nz,←Nat.cast_tsub]
  have prev : epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (predecessorRadius n j)
      ≤ 1/(Q:ℝ≥0∞) := by
    apply (GeneralManyLineSafety.epsMCA_le (e:=j-1) (t:=n-j+1) (r:=m) x _
      (Fintype.card_fin _) (by omega) (by omega) (by omega) scale heads ?_ ?_ geometry).trans
    · rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos Qpos,Nat.sub_add_cancel positive,index,Nat.mul_comm]
      exact Nat.div_mul_le_self ..
    · unfold predecessorRadius
      rw [Fintype.card_fin,grid _ (by omega),Nat.ceil_natCast]
      omega
    · rwa [show j-1+2=j+1 by omega]
  have result := le_antisymm (mcaDeltaStar_le_of_bad _ _ bad)
    (latticeBoundary_le_mcaDeltaStar_of_predecessor_good positive inside _ _ prev)
  refine ⟨result,fun δ => ⟨fun h => ?_,fun h => ?_⟩⟩
  · by_contra! outside
    exact bad.not_ge ((epsMCA_mono _ outside).trans h)
  · by_contra! fail
    exact h.not_ge (result ▸ mcaDeltaStar_le_of_bad _ _ fail)


/-- The predecessor passes for every received pair and the next integer step
fails on every prescribed domain satisfying the two finite counting tests. -/
theorem exact_threshold {n k m Q j L : ℕ} [NeZero n] (x : Fin n ↪ F)
    (Qpos : 0 < Q) (heads : 1 ≤ m) (index : j=Fintype.card F/Q/m) (positive : 0 < j)
    (inside : j≤n) (degree : 2≤k) (agree : k<n-j) (scale : 2≤L)
    (moment : (j+1)*k*n^2+(L+2)*n^3 < (j+1)*(n-j+1)^3)
    (geometry : (n+(m.choose 2+m)*k)*L+m*n < (m+1)*(n-j+1)*L)
    (pack : m*(n-j-k+1) ≤ n-k+2)
    (room : n^2*(m+1)^4 ≤ (Fintype.card F-1)*(k-2)) :
    let C := (ReedSolomon.code x k : Set (Fin n → F))
    let ε := 1/(Q:ℝ≥0∞)
    let bound := (j:ℝ≥0)/n
    mcaDeltaStar (F:=F) C ε = bound ∧ ∀ δ, epsMCA (F:=F) C δ ≤ ε ↔ δ < bound := by
  dsimp only
  have nz : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have grid (e : ℕ) (he : e≤n) : (1-(e:ℝ≥0)/n)*(n:ℝ≥0) = ((n-e:ℕ):ℝ≥0) := by
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ nz,←Nat.cast_tsub]
  apply exact_threshold_of_bad x Qpos heads index positive inside degree agree scale moment geometry
  apply lt_of_lt_of_le _ (ArbitraryDomainHeadMass.grid_mass (t:=n-j) (m:=m)
      x _ heads degree agree (by omega) pack ((grid _ inside).le) room)
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos Qpos,show n-(n-j)+1=j+1 by omega,index]
  exact Nat.not_le_of_lt (Nat.lt_mul_div_succ _ heads)

end ProximityGap.ArbitraryDomainHeadThreshold
#print axioms ProximityGap.ArbitraryDomainHeadThreshold.exact_threshold
#print axioms ProximityGap.ArbitraryDomainHeadThreshold.exact_threshold_of_bad
