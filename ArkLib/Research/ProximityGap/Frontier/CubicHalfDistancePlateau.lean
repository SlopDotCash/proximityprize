/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CubicSpikeBudgetBoundary
import ArkLib.Research.ProximityGap.Frontier.OddRedundancyApolar

/-! # Finite half-distance plateau through rate one half

For even redundancy 2h and dimension at most 2h+4, the cubic apolar
estimate leaves at most two integer budgets undecided below 2h+2.
At those budgets the two possible first failures are consecutive.
-/
set_option autoImplicit false
namespace ProximityGap.CubicHalfDistancePlateau
open MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k h : ℕ} [NeZero n]

/-- At h−1 errors, the largest admissible cubic count is the least
multiple of three greater than or equal to h. -/
def cap (h : ℕ) : ℕ := 3*((h+2)/3)

private theorem cubic (x : Fin n ↪ F) {e : ℕ} (length : n=k+2*h)
    (hk : 2 ≤ k) (rate : k ≤ 2*h+4) (big : 4 ≤ h) (err : e<h) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) ≤
      ((max (e+1) (3*(e/(2*h+1-2*e)+1)):ℕ):ℝ≥0∞)/Fintype.card F := by
  apply epsMCA_le_of_badCount_le
  intro W
  have lim := CubicApolarExtremum.count_bound x k e (2*h-1) (by omega) (by omega) (by omega)
    (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega) (W 0) (W 1)
  rw [Fintype.card_fin,show 2*h-1+2=2*h+1 by omega] at lim
  exact lim

/-- Before the predecessor, the spike is extremal on every evaluation domain. -/
theorem preunique_mass (x : Fin n ↪ F) {e : ℕ} (length : n=k+2*h)
    (hk : 2 ≤ k) (rate : k ≤ 2*h+4) (big : 4 ≤ h) (err : e ≤ h-2) :
    epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) ((e:ℝ≥0)/n) =
      ((e+1:ℕ):ℝ≥0∞)/Fintype.card F := by
  apply le_antisymm _ (LinearFieldBudgetRadius.spike x (by omega))
  by_cases small : e ≤ 1
  · rw [← BoundarySecurityBudget.rsCode_eq_code]
    apply SpikeFloor.epsMCA_le_j_div_card (j:=e+1) (SpikeFloor.rsCode x k)
      (SpikeFloor.rsCode_noWeightLE x (by omega))
    have nz : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Fintype.card_fin,div_mul_cancel₀ _ nz]
    exact_mod_cast Nat.lt_succ_self e
  have est := cubic x length hk rate big (by omega : e<h)
  have bound := Nat.div_le_div_left (a:=e) (by omega : 5 ≤ 2*h+1-2*e) (by decide : 0<5)
  rwa [max_eq_left (by omega : 3*(e/(2*h+1-2*e)+1) ≤ e+1)] at est

/-- The two candidate counts at the end of the spike range differ by at most two. -/
theorem endpoint_bounds (x : Fin n ↪ F) (length : n=k+2*h)
    (hk : 2 ≤ k) (rate : k ≤ 2*h+4) (big : 4 ≤ h) :
    let M := epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n)
    (h:ℝ≥0∞)/Fintype.card F ≤ M ∧ M ≤ (cap h:ℝ≥0∞)/Fintype.card F := by
  dsimp only
  constructor
  · simpa only [show h-1+1=h by omega] using LinearFieldBudgetRadius.spike (k:=k) (e:=h-1) x (by omega)
  · have b := cubic x length hk rate big (by omega : h-1<h)
    rwa [show max (h-1+1) (3*((h-1)/(2*h+1-2*(h-1))+1))=cap h by
      unfold cap
      rw [show 2*h+1-2*(h-1)=3 by omega]
      omega] at b

/-- The first failing index in the finite plateau is selected by exactly one
endpoint comparison when the budget lies within two of h. -/
noncomputable def index (x : Fin n ↪ F) (k h B Q : ℕ) : ℕ := by
  classical
  exact if B<h then B else if epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F))
    (((h-1:ℕ):ℝ≥0)/n) ≤ 1/(Q:ℝ≥0∞) then h else h-1

/-- All positive widths and all real radii, including a zero budget. -/
theorem classification (x : Fin n ↪ F) {B Q : ℕ} (length : n=k+2*h)
    (hk : 2 ≤ k) (rate : k ≤ 2*h+4) (big : 4 ≤ h) (pos : 0<Q)
    (budget : Fintype.card F/Q=B) (range : B ≤ 2*h+1) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code x k : Set (Fin n → F)) ^⋈ (Fin width)
    let j := index x k h B Q
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞)) = (j:ℝ≥0)/n ∧
      ∀ δ, epsMCA (F:=F) C δ ≤ 1/(Q:ℝ≥0∞) ↔ δ<(j:ℝ≥0)/n := by
  classical
  let C := (ReedSolomon.code x k : Set (Fin n → F))
  let j := index x k h B Q
  have ratio (a : ℕ) : (a:ℝ≥0∞)/Fintype.card F ≤ 1/(Q:ℝ≥0∞) ↔ a ≤ B :=
    budget ▸ BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos pos
  have jle : j ≤ h := by unfold j index; split_ifs <;> omega
  have bad : 1/(Q:ℝ≥0∞) < epsMCA (F:=F) C ((j:ℝ≥0)/n) := by
    unfold j index
    split_ifs with small safe
    · apply lt_of_lt_of_le _ (LinearFieldBudgetRadius.spike x (k:=k) (e:=B) (by omega))
      exact lt_of_not_ge (fun h' => (Nat.not_succ_le_self B) ((ratio _).mp h'))
    · have attack := TwoHeadLinearBudget.errors (k:=k) (e:=h) x
        (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
      rw [Fintype.card_fin] at attack
      apply lt_of_lt_of_le _ attack
      exact lt_of_not_ge (fun h' => (by omega : ¬2*(h+1)≤B) ((ratio _).mp h'))
    · exact lt_of_not_ge safe
  have prev (jp : 0<j) : epsMCA (F:=F) C (((j-1:ℕ):ℝ≥0)/n) ≤ 1/(Q:ℝ≥0∞) := by
    unfold j index at jp ⊢
    split_ifs with small safe
    · have bp : 0 < B := by simpa [small] using jp
      exact (preunique_mass x length hk rate big (by omega : B-1≤h-2)).le.trans ((ratio _).mpr (by omega))
    · exact safe
    · exact (preunique_mass x length hk rate big (by omega : h-1-1≤h-2)).le.trans ((ratio _).mpr (by omega))
  have exact_radius : mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞)) = (j:ℝ≥0)/n := by
    by_cases zero : j=0
    · exact le_antisymm (mcaDeltaStar_le_of_bad C _ bad) (by simp [zero])
    · exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
        (a:=j) (by omega) (by omega) C _ (prev (by omega)) bad
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  refine ⟨exact_radius,?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! outside
    exact bad.not_ge ((epsMCA_mono C outside).trans good)
  · intro inside
    by_contra! fails
    exact inside.not_ge (exact_radius ▸ mcaDeltaStar_le_of_bad C _ fails)

/-- Away from at most two integer budgets the index has no remaining
code-dependent comparison. -/
theorem index_eq_min (x : Fin n ↪ F) {B Q : ℕ} (length : n=k+2*h)
    (hk : 2 ≤ k) (rate : k ≤ 2*h+4) (big : 4 ≤ h) (pos : 0<Q)
    (budget : Fintype.card F/Q=B) (regular : B<h ∨ cap h ≤ B) : index x k h B Q = min B h := by
  classical
  unfold index
  split_ifs with small safe
  · omega
  · omega
  · have le := (endpoint_bounds x length hk rate big).2
    have fit : cap h ≤ Fintype.card F/Q := by rw [budget];omega
    exact False.elim (safe (le.trans ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos pos).mpr fit)))

end ProximityGap.CubicHalfDistancePlateau
#print axioms ProximityGap.CubicHalfDistancePlateau.preunique_mass
#print axioms ProximityGap.CubicHalfDistancePlateau.classification
#print axioms ProximityGap.CubicHalfDistancePlateau.index_eq_min
