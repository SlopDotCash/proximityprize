/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.RankBoundary
import ArkLib.Research.ProximityGap.Frontier.ListSupportRank
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportRank
import ArkLib.Research.ProximityGap.Collapse

/-! # Exact operational boundaries from finite support-rank tests

For each error count, the MCA test ranges over sets of scalar challenges and their assigned
supports. The list test ranges over supports and edge sets recording collisions. Both use
linear dimensions. The tests quantify over no received words or centers. The finite scans
and inclusion–exclusion sums can grow exponentially or faster in the supplied parameters.
These formulas give no practical running-time guarantee.
-/
set_option autoImplicit false

namespace ProximityPrize.RankReview
open Code ProximityGap ProximityGap.GrandChallenges CoreDefinitions FullPrizeReview RankBoundary
open scoped NNReal ENNReal BigOperators

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- Maximum permitted integer count for the field and tolerance, shared by both tests. -/
noncomputable def budget (F : Type) [Fintype F] (ε : ℝ≥0) : ℕ :=
  ⌊ε * (Fintype.card F : ℝ≥0)⌋₊

/-- Test for simultaneous feasibility of more bad scalars than the budget permits. -/
def mcaFails (D : I ↪ F) (k B : ℕ) (e : Fin (Fintype.card I + 1)) : Prop :=
  ∃ (G : Finset F) (_ : G.card = B + 1) (S : G → Finset I),
    (∀ g, Fintype.card I - e.val ≤ (S g).card) ∧
    ∀ g, Module.finrank F ↥(SimultaneousSupportRank.space (ReedSolomon.code D k) G S ⊓
      SimultaneousSupportRank.jointSpace (ReedSolomon.code D k) (S g)) <
      Module.finrank F (SimultaneousSupportRank.space (ReedSolomon.code D k) G S)

/-- Test for a positive number of distinct compatible lists in a fixed support pattern. -/
def listFails (D : I ↪ F) (k m B : ℕ) (e : Fin (Fintype.card I + 1)) : Prop :=
  ∃ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = Fintype.card I - e.val) ∧
    0 < ∑ T ∈ ((Finset.univ : Finset (Fin (B + 1) × Fin (B + 1))).filter
      (fun p => p.1 < p.2)).powerset, (-1 : ℤ) ^ T.card * (Fintype.card F : ℤ) ^
      (Module.finrank F (ListSupportRank.vandermonde D k S T).ker * m)

/-- The first error count having a simultaneous rank-increase certificate, if one exists. -/
noncomputable def mcaAnswer (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) : Boundary (Fintype.card I) :=
  firstFailure _ (mcaFails D k (budget F ε))

/-- The first error count with a positive inclusion–exclusion rank sum, if one exists. -/
noncomputable def listAnswer (D : I ↪ F) (ε : ℝ≥0) (k m : ℕ) : Boundary (Fintype.card I) :=
  firstFailure _ (listFails D k m (budget F ε))

variable [Nonempty I]

omit [DecidableEq F] [DecidableEq I] in
private theorem list_grid (D : I ↪ F) (ε : ℝ≥0) (k m : ℕ) (hk : k ≤ Fintype.card I)
    (e : Fin (Fintype.card I + 1)) :
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
      (gridPt (ι := I) e.val : ℝ) : ENNReal) ≤ (ε : ENNReal) * Fintype.card F ↔
      ¬ listFails D k m (budget F ε) e := by
  have he : e.val ≤ Fintype.card I := Nat.le_of_lt_succ e.isLt
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hrad : (gridPt (ι := I) e.val : ℝ) =
      1 - ((Fintype.card I - e.val : ℕ) : ℝ) / Fintype.card I := by
    simp only [gridPt, NNReal.coe_div, NNReal.coe_natCast, Nat.cast_sub he]
    field_simp
    ring
  refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
    (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) _ ε).trans ?_
  rw [hrad]
  refine (ListSupportRank.rs_vandermonde_safe_iff D k m (budget F ε) _
    Fintype.card_pos hk).trans ?_
  unfold listFails budget
  push Not
  rfl

omit [DecidableEq F] [DecidableEq I] in
open scoped Classical in
private theorem mca_grid (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) (e : Fin (Fintype.card I + 1)) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) (gridPt (ι := I) e.val) ≤
      (ε : ENNReal) ↔ ¬ mcaFails D k (budget F ε) e := by
  classical
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
  rw [← not_lt, SimultaneousSupportRank.budget_failure_iff]
  unfold mcaFails budget
  have hcard (S : Finset I) :
      ((1 - gridPt (ι := I) e.val) * Fintype.card I ≤ (S.card : ℝ≥0)) ↔
      Fintype.card I - e.val ≤ S.card := by
    rw [← relDist_floor_bound_iff_complement_bound, gridPt_mul_card, Nat.floor_natCast]
  simp_rw [ge_iff_le, hcard]

/-- The finite support-rank formulas classify every radius in the unit interval, at all prize
rates and all positive interleaving widths, for any supplied field, smooth domain and tolerance. -/
theorem correctForEveryDomain [SampleableType F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) :
    correctForDomain D ε (mcaAnswer D ε) (listAnswer D ε) := by
  intro k hk
  have hk' : k ≤ Fintype.card I := by
    rcases hk with h | h | h | h <;> omega
  constructor
  · unfold mcaAnswer
    simp_rw [← epsMCA_eq_mcaError]
    apply firstFailure_correct_of_grid Fintype.card_pos
    · intro a b hab hb
      exact (epsMCA_mono _ hab).trans hb
    · intro a b hab
      rw [epsMCA_eq_of_floor_eq _ hab]
    · exact mca_grid D ε k
  · intro m _
    unfold listAnswer
    apply firstFailure_correct_of_grid Fintype.card_pos
    · intro a b hab hb
      exact (lambda_mono_nnreal hab).trans hb
    · intro a b hab
      rw [lambda_eq_of_floor_eq (C := interleavedCodeSet (κ := Fin m)
        (ReedSolomon.code D k : Set (I → F))) hab]
    · exact list_grid D ε k m hk'

#print axioms correctForEveryDomain
end ProximityPrize.RankReview
