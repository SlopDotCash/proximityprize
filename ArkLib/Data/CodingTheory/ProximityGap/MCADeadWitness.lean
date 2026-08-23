/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StackJointAgreement
import ArkLib.Data.CodingTheory.ProximityLeaves2

/-!
# Dead MCA witnesses for Reed-Solomon codes (#357)

For a Reed-Solomon code of degree `< k`, every prescription on at most `k` domain points
interpolates to a codeword. Consequently a putative MCA witness set of size `≤ k` is
automatically jointly explainable row-by-row, so `mcaEvent` can only fire on witness sets
with more than `k` points.
-/

open scoped NNReal

namespace ProximityGap

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Any stack of words jointly agrees with Reed-Solomon codewords on a set of at most `k`
coordinates: interpolate each row independently through the set. -/
theorem stackJointAgreesOn_rs_of_card_le {κ : Type} (domain : ι ↪ F)
    {k : ℕ} {S : Finset ι} (hS : S.card ≤ k) (u : κ → ι → F) :
    stackJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u := by
  rw [stackJointAgreesOn_iff_forall_row]
  intro j
  exact ReedSolomon.ReedSolomon_interpolate_through_subset domain S hS (u j)

/-- Pair form of `stackJointAgreesOn_rs_of_card_le`, matching the affine-line MCA API. -/
theorem pairJointAgreesOn_rs_of_card_le (domain : ι ↪ F)
    {k : ℕ} {S : Finset ι} (hS : S.card ≤ k) (u₀ u₁ : ι → F) :
    pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁ := by
  simpa [stackJointAgreesOn_pair_iff]
    using stackJointAgreesOn_rs_of_card_le (κ := Fin 2) domain hS ![u₀, u₁]

/-- Dead-witness elimination: an MCA event for `RS(domain,k)` must use a witness set with
strictly more than `k` coordinates. Sets of size `≤ k` are rowwise interpolable and hence
cannot satisfy the `¬ pairJointAgreesOn` clause. -/
theorem mcaEvent_rs_exists_witness_card_gt (domain : ι ↪ F) {k : ℕ} {δ : ℝ≥0}
    {u₀ u₁ : ι → F} {γ : F}
    (h : mcaEvent (F := F) (A := F)
      (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ γ) :
    ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        k < S.card ∧
        (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)),
          ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn (ReedSolomon.code domain k : Set (ι → F)) S u₀ u₁ := by
  rcases h with ⟨S, hcard, hclose, hno⟩
  have hklt : k < S.card := by
    by_contra hnot
    exact hno (pairJointAgreesOn_rs_of_card_le domain (Nat.le_of_not_gt hnot) u₀ u₁)
  exact ⟨S, hcard, hklt, hclose, hno⟩

end ProximityGap

/-! ## Axiom audit -/

#print axioms ProximityGap.stackJointAgreesOn_rs_of_card_le
#print axioms ProximityGap.pairJointAgreesOn_rs_of_card_le
#print axioms ProximityGap.mcaEvent_rs_exists_witness_card_gt
