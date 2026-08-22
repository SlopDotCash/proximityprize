/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit

/-!
# LANE HLOW (#466 round 159): the punctured unique-decoding slice

The HLOW map notes that the large-zero appearing list is a punctured RS list-decoding ball on the
zero set `Z = directionZeroSet u₁`: every appearing codeword agrees with the offset `u₀` on at least
`a - #support(u₁)` coordinates inside `Z`.

This file formalizes the elementary unique-decoding slice of that picture.  If two such
zero-agreement sets must overlap in at least `k` coordinates,

`#Z + k ≤ 2 * (a - #support(u₁))`,

then MDS uniqueness forces the whole appearing list to have size at most one.  This is often empty
at prize parameters, so it is not a closure; it is the clean boundary where the punctured-list
residual becomes genuinely trivial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Finset

namespace ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LargeZeroWitnessSplit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- If two codewords each agree with `u₀` on at least `m` coordinates of the same zero set `Z`,
and `#Z + k ≤ 2m`, then they agree with each other on at least `k` coordinates. -/
theorem zeroAgreement_inter_card_ge
    {k m : ℕ} {u₀ u₁ c c' : Fin n → F}
    (hthr : (directionZeroSet u₁).card + k ≤ 2 * m)
    (hc : m ≤ (directionZeroAgreementSet c u₀ u₁).card)
    (hc' : m ≤ (directionZeroAgreementSet c' u₀ u₁).card) :
    k ≤ (directionZeroAgreementSet c u₀ u₁ ∩
      directionZeroAgreementSet c' u₀ u₁).card := by
  have hsub : directionZeroAgreementSet c u₀ u₁ ∪
      directionZeroAgreementSet c' u₀ u₁ ⊆ directionZeroSet u₁ := by
    intro i hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact (Finset.filter_subset _ _) hi
    · exact (Finset.filter_subset _ _) hi
  have hunion : (directionZeroAgreementSet c u₀ u₁ ∪
      directionZeroAgreementSet c' u₀ u₁).card ≤ (directionZeroSet u₁).card :=
    Finset.card_le_card hsub
  have hkey := Finset.card_inter_add_card_union
    (directionZeroAgreementSet c u₀ u₁) (directionZeroAgreementSet c' u₀ u₁)
  omega

open Classical in
/-- On the punctured unique-decoding slice, the appearing-codeword list of a large-zero line has
size at most one.  The premise is the punctured-code unique-decoding inequality with radius
`#Z - (a - #support)`:
`#Z + k ≤ 2 * (a - #support)`. -/
theorem lineAppearingCodewords_card_le_one_of_punctured_unique
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hthr : (directionZeroSet u₁).card + k
      ≤ 2 * (a - (directionSupportSet u₁).card)) :
    (lineAppearingCodewords dom k a u₀ u₁).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro c hc c' hc'
  by_contra hne
  have hcz := sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
    dom k a u₀ u₁ hc
  have hc'z := sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
    dom k a u₀ u₁ hc'
  have hinter : k ≤ (directionZeroAgreementSet c u₀ u₁ ∩
      directionZeroAgreementSet c' u₀ u₁).card :=
    zeroAgreement_inter_card_ge (k := k) (m := a - (directionSupportSet u₁).card)
      hthr hcz hc'z
  have hpair : directionZeroAgreementSet c u₀ u₁ ∩
      directionZeroAgreementSet c' u₀ u₁ ⊆ agreeSet c c' := by
    intro i hi
    rw [Finset.mem_inter] at hi
    obtain ⟨hi, hi'⟩ := hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi hi'
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2.trans hi'.2.symm⟩
  have hmono : (directionZeroAgreementSet c u₀ u₁ ∩
      directionZeroAgreementSet c' u₀ u₁).card ≤ (agreeSet c c').card :=
    Finset.card_le_card hpair
  have hcode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  have hcode' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc'
    exact hc'.2.1
  have hcap : (agreeSet c c').card ≤ k - 1 :=
    rsCode_pairwise_agreeSet_card_le dom hk hcode hcode' hne
  omega

end ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice.zeroAgreement_inter_card_ge
#print axioms
  ProximityGap.LargeZeroWitnessSplit.Frontier.R159PuncturedUniqueDecodingSlice.lineAppearingCodewords_card_le_one_of_punctured_unique
