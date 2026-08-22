/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonResidualFloor

/-!
# SubJohnsonSupplyReframe

Module docstring for `SubJohnsonSupplyReframe.lean`.
-/


open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The per-word capped supply value: the number of explainable `(k+m+1)`-cores
of a word `w`. -/
noncomputable def cappedSupplyOf (dom : Fin n ↪ F) (k m : ℕ) (w : Fin n → F) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => ExplainableOn dom k w T)).card

open Classical in
/-- An admissible word for the capped residual: all codeword agreements `≤ 2k+m+1`. -/
def CappedAdmissible (dom : Fin n ↪ F) (k m : ℕ) (w : Fin n → F) : Prop :=
  ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
    (agreeSet c w).card ≤ 2 * k + m + 1

/-- Restating the residual in terms of the per-word value. -/
theorem subJohnsonSupplyResidual_iff_forall (dom : Fin n ↪ F) (k m B : ℕ) :
    SubJohnsonSupplyResidual dom k m B
      ↔ ∀ w : Fin n → F, CappedAdmissible dom k m w → cappedSupplyOf dom k m w ≤ B := by
  rfl

open Classical in
/-- **The optimal capped supply**: the largest core count over all admissible
words (a finite sup, since `Fin n → F` is finite).  This is the single number
whose value IS the open content of the residual: `SubJohnsonSupplyResidual dom k
m B` holds iff `B` dominates it. -/
noncomputable def cappedSupplyOptimal (dom : Fin n ↪ F) (k m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → F)).filter (CappedAdmissible dom k m)).sup
    (cappedSupplyOf dom k m)

open Classical in
/-- **The residual is a single number**: `SubJohnsonSupplyResidual dom k m B`
holds exactly when `B` dominates the optimal capped supply.  Reduces the
quantified open statement to a numeric one. -/
theorem subJohnsonSupplyResidual_iff_optimal_le (dom : Fin n ↪ F) (k m B : ℕ) :
    SubJohnsonSupplyResidual dom k m B
      ↔ cappedSupplyOptimal dom k m ≤ B := by
  rw [subJohnsonSupplyResidual_iff_forall, cappedSupplyOptimal, Finset.sup_le_iff]
  constructor
  · intro h w hw
    exact h w ((Finset.mem_filter.mp hw).2)
  · intro h w hw
    exact h w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)

open Classical in
/-- **The pair-count ceiling on the optimal supply**: unconditionally
`cappedSupplyOptimal dom k m ≤ C(n,k)`. -/
theorem cappedSupplyOptimal_le_pairCount (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) :
    cappedSupplyOptimal dom k m ≤ n.choose k :=
  (subJohnsonSupplyResidual_iff_optimal_le dom k m (n.choose k)).mp
    (subJohnsonSupplyResidual_pairCount dom hk)

open Classical in
/-- **The per-word class floor on the value**: any word constant `= v` on a set
`S` has `cappedSupplyOf ≥ C(|S|, k+m+1)`. -/
theorem class_floor_cappedSupplyOf (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    {w : Fin n → F} {S : Finset (Fin n)} {v : F} (hconst : ∀ i ∈ S, w i = v) :
    S.card.choose (k + m + 1) ≤ cappedSupplyOf dom k m w :=
  class_supply_floor dom hk m hconst

open Classical in
/-- **The optimal supply dominates any admissible word's value**. -/
theorem cappedSupplyOf_le_optimal (dom : Fin n ↪ F) (k m : ℕ)
    {w : Fin n → F} (hw : CappedAdmissible dom k m w) :
    cappedSupplyOf dom k m w ≤ cappedSupplyOptimal dom k m :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)

open Classical in
/-- **The class floor on the OPTIMAL supply from a ±1 word.**  For any
admissible `{1,−1}`-valued word whose value classes both fit under the agreement
cap, the optimal capped supply is at least `C(s₊, k+m+1)`. -/
theorem cappedSupplyOptimal_pm_one_floor (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) (m : ℕ) {w : Fin n → F} (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hcap1 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card
      ≤ 2 * k + m + 1)
    (hcap2 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = -1)).card
      ≤ 2 * k + m + 1) :
    (((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card).choose (k + m + 1)
      ≤ cappedSupplyOptimal dom k m := by
  classical
  -- admissibility of the ±1 word via the proven pm-one agreement cap
  have hadm : CappedAdmissible dom k m w := by
    intro c hc
    refine le_trans ?_ (le_trans (pm_one_agreement_le dom hk hw hc)
      (max_le (by omega) (max_le hcap1 hcap2)))
    -- `(agreeSet c w).card = (filter (c i = w i)).card` by `agreeSet` defeq
    exact le_of_eq rfl
  refine le_trans ?_ (cappedSupplyOf_le_optimal dom k m hadm)
  exact class_floor_cappedSupplyOf dom hk m
    (S := (Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)) (v := 1)
    (fun i hi => (Finset.mem_filter.mp hi).2)

open Classical in
/-- **THE TWO-SIDED BRACKET on the optimal capped supply (#389).**  For every
admissible balanced `{1,−1}`-valued word `w` (both value classes `≤ 2k+m+1`),
the optimal capped supply is bracketed

  `C(s₊, k+m+1)  ≤  cappedSupplyOptimal dom k m  ≤  C(n, k)`,

with `s₊` the size of the `+1` class.  The right edge (`C(n,k)`, the
pair-count ceiling) is unconditional; the left edge is the proven class floor
realized by the character/coset family.  The open content is exactly the value
in this window — every face of the sub-Johnson list-size wall is the question
"where in `[C(s₊,k+m+1), C(n,k)]` does this single number sit?". -/
theorem cappedSupplyOptimal_two_sided_bracket (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) (m : ℕ) {w : Fin n → F} (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hcap1 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card
      ≤ 2 * k + m + 1)
    (hcap2 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = -1)).card
      ≤ 2 * k + m + 1) :
    (((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card).choose (k + m + 1)
        ≤ cappedSupplyOptimal dom k m
      ∧ cappedSupplyOptimal dom k m ≤ n.choose k :=
  ⟨cappedSupplyOptimal_pm_one_floor dom hk m hw hcap1 hcap2,
    cappedSupplyOptimal_le_pairCount dom hk⟩

open Classical in
/-- **The optimal supply is the LEAST valid `B`** (the residual's minimal
admissible bound is exactly `cappedSupplyOptimal`): it satisfies the residual,
and is dominated by every `B` that does. -/
theorem cappedSupplyOptimal_is_least (dom : Fin n ↪ F) (k m : ℕ) :
    SubJohnsonSupplyResidual dom k m (cappedSupplyOptimal dom k m)
      ∧ ∀ B, SubJohnsonSupplyResidual dom k m B → cappedSupplyOptimal dom k m ≤ B :=
  ⟨(subJohnsonSupplyResidual_iff_optimal_le dom k m _).mpr le_rfl,
    fun B hB => (subJohnsonSupplyResidual_iff_optimal_le dom k m B).mp hB⟩

end ProximityGap.PairRank

#print axioms ProximityGap.PairRank.subJohnsonSupplyResidual_iff_forall
#print axioms ProximityGap.PairRank.subJohnsonSupplyResidual_iff_optimal_le
#print axioms ProximityGap.PairRank.cappedSupplyOptimal_le_pairCount
#print axioms ProximityGap.PairRank.class_floor_cappedSupplyOf
#print axioms ProximityGap.PairRank.cappedSupplyOf_le_optimal
#print axioms ProximityGap.PairRank.cappedSupplyOptimal_pm_one_floor
#print axioms ProximityGap.PairRank.cappedSupplyOptimal_two_sided_bracket
#print axioms ProximityGap.PairRank.cappedSupplyOptimal_is_least
