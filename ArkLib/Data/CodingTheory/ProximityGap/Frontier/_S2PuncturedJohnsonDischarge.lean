/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.CodeGeometry
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LowProfileFiberCoupled

/-!
# S2: within-Johnson discharge of the punctured list budget (#466)

**Mechanism.** The surviving sub-`q` object on the large-zero branch is
`PuncturedListBudget` (`_LowProfileFiberCoupled.lean` §6): a direct cap on the appearing-list
size `Λ = #lineAppearingCodewords` on large-zero safe lines.  This file discharges it **inside
the Johnson regime of the punctured parameters** by an honest three-step weld:

1. **Witness split** (`sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords`,
   `_R2B_LargeZeroWitnessSplit.lean`): every appearing codeword agrees with the offset `u₀` on
   at least `a − s` coordinates of the zero set `Z := directionZeroSet u₁` (`s := #support`).
2. **Puncture**: restrict everything to `Z`.  Restricted distinct RS codewords still agree
   pairwise on at most `k − 1` coordinates (`rsCode_pairwise_agreeSet_card_le` — the agreement
   set inside `Z` is a subset of the global one), and each restricted appearing codeword agrees
   with `u₀|_Z` on `≥ a − s` of the `z := #Z` coordinates.
3. **Johnson cap** (`CodeGeometry.card_le_of_johnson_sq`, the radical-free ABF26 Thm 3.2 form
   on the coordinate type `↥Z`): under the squared Johnson condition
   `(ℓ+1)·(A − z/q)² > N·(N + ℓ·((k−1) − z/q))` with `A := a − s`, `N := z(1 − 1/q)`,
   the appearing list has size `≤ ℓ`.

Payload: `lineAppearingCodewords_card_le_of_punctured_johnson` (per-line form) and the uniform
packaging `puncturedListBudget_of_johnson` producing the named
`ProximityGap.LowProfileCoupled.PuncturedListBudget` object under a per-line Johnson-condition
window hypothesis.  A numeric sanity check (`johnson_condition_sanity`) confirms the squared
condition is satisfiable at small parameters (`z = 4, q = 5, A = 3, k − 1 = 1, ℓ = 2`).

**Honest scope.** This is the *within-Johnson* discharge plus boundary pin only: the cap is
available exactly when the punctured parameters `(z, a − s, k − 1)` sit inside the (squared)
Johnson region.  The beyond-Johnson band `(a − s)² ≤ z·(k − 1)` (up to the `1/q` corrections)
remains THE open core, and by `docs/kb/deltastar-466b-hlow-map-2026-07-01.md` §3 it is the SAME
beyond-Johnson list-size problem as the far branch H1 — Johnson-equivalent-hard.  Nothing here
touches the prize wall; it seals the tractable side of the split.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, lane S2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PuncturedJohnsonDischarge

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LargeZeroWitnessSplit ProximityGap.LowProfileCoupled

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ### 1. Restriction bookkeeping: `CodeGeometry.agree` on a punctured coordinate set -/

open Classical in
/-- Agreement of two words restricted to a coordinate subset `Z` equals the size of the
in-`Z` agreement filter.  This is the dictionary between the Gram-matrix agreement count of
`CodeGeometry` (on the subtype `↥Z`) and the ambient filter sets. -/
theorem agree_restrict_eq (Z : Finset (Fin n)) (w w' : Fin n → F) :
    CodeGeometry.agree (fun i : ↥Z => w i.1) (fun i : ↥Z => w' i.1)
      = (Z.filter (fun i => w i = w' i)).card := by
  classical
  rw [CodeGeometry.agree]
  refine Finset.card_bij (fun (i : ↥Z) _ => i.1) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨i.2, hi.2⟩
  · intro i _ j _ h
    exact Subtype.ext h
  · intro j hj
    rw [Finset.mem_filter] at hj
    exact ⟨⟨j, hj.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩, rfl⟩

open Classical in
/-- The in-`Z` agreement of two words is at most their global agreement. -/
theorem filter_card_le_agreeSet_card (Z : Finset (Fin n)) (w w' : Fin n → F) :
    (Z.filter (fun i => w i = w' i)).card ≤ (agreeSet w w').card := by
  classical
  refine Finset.card_le_card ?_
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [agreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hi.2⟩

/-! ### 2. The per-line within-Johnson discharge -/

open Classical in
/-- **Per-line punctured Johnson cap.**  For any affine line `(u₀, u₁)` with nonempty zero set
`Z := directionZeroSet u₁` (`z := #Z`, `s := #support`), if the punctured parameters satisfy the
squared Johnson condition of `CodeGeometry.card_le_of_johnson_sq` with center agreement
`A := a − s`, pairwise agreement `B := k − 1`, and block length `z`, then the appearing list of
the line has size at most `ℓ`.  The witness split supplies `A`, RS pairwise agreement supplies
`B`, and the puncture to `↥Z` supplies the block. -/
theorem lineAppearingCodewords_card_le_of_punctured_johnson
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (u₀ u₁ : Fin n → F)
    (hq1 : 1 < Fintype.card F)
    (hz : 0 < (directionZeroSet u₁).card)
    (ℓ : ℕ)
    (hP : ((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)
        ≤ ((a - (directionSupportSet u₁).card : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((a - (directionSupportSet u₁).card : ℕ) : ℝ)
            - ((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > (((directionZeroSet u₁).card : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((directionZeroSet u₁).card : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((k - 1 : ℕ) : ℝ)
                - ((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)))) :
    (lineAppearingCodewords dom k a u₀ u₁).card ≤ ℓ := by
  classical
  set Z : Finset (Fin n) := directionZeroSet u₁ with hZ
  set S : Finset (Fin n → F) := lineAppearingCodewords dom k a u₀ u₁ with hS
  by_cases hL0 : S.card = 0
  · exact hL0 ▸ Nat.zero_le ℓ
  · have hL : 0 < S.card := Nat.pos_of_ne_zero hL0
    let e : Fin S.card ≃ {x // x ∈ S} := S.equivFin.symm
    -- restricted family and restricted center
    let c : Fin S.card → (↥Z → F) := fun i j => (e i).1 j.1
    let f : ↥Z → F := fun j => u₀ j.1
    have hcardZ : Fintype.card ↥Z = Z.card := Fintype.card_coe Z
    -- center agreement from the witness split
    have hA : ∀ i, (a - (directionSupportSet u₁).card)
        ≤ CodeGeometry.agree (c i) f := by
      intro i
      have hmem : ((e i) : Fin n → F) ∈ lineAppearingCodewords dom k a u₀ u₁ := by
        rw [← hS]; exact (e i).2
      have h1 := sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
        dom k a u₀ u₁ hmem
      have h2 : (directionZeroAgreementSet ((e i) : Fin n → F) u₀ u₁).card
          = (Z.filter (fun t => ((e i) : Fin n → F) t = u₀ t)).card := by
        rw [directionZeroAgreementSet, hZ]
      have h3 := agree_restrict_eq Z ((e i) : Fin n → F) u₀
      calc a - (directionSupportSet u₁).card
          ≤ (directionZeroAgreementSet ((e i) : Fin n → F) u₀ u₁).card := h1
        _ = (Z.filter (fun t => ((e i) : Fin n → F) t = u₀ t)).card := h2
        _ = CodeGeometry.agree (c i) f := h3.symm
    -- pairwise agreement from RS uniqueness on the puncture
    have hB : ∀ i j, i ≠ j → CodeGeometry.agree (c i) (c j) ≤ k - 1 := by
      intro i j hij
      have hne : ((e i) : Fin n → F) ≠ ((e j) : Fin n → F) := by
        intro h
        exact hij (e.injective (Subtype.ext h))
      have hmi : ((e i) : Fin n → F) ∈ lineAppearingCodewords dom k a u₀ u₁ := by
        rw [← hS]; exact (e i).2
      have hmj : ((e j) : Fin n → F) ∈ lineAppearingCodewords dom k a u₀ u₁ := by
        rw [← hS]; exact (e j).2
      rw [lineAppearingCodewords, Finset.mem_filter] at hmi hmj
      have hci : ((e i) : Fin n → F) ∈ (rsCode dom k : Submodule F (Fin n → F)) := hmi.2.1
      have hcj : ((e j) : Fin n → F) ∈ (rsCode dom k : Submodule F (Fin n → F)) := hmj.2.1
      calc CodeGeometry.agree (c i) (c j)
          = (Z.filter (fun t => ((e i) : Fin n → F) t = ((e j) : Fin n → F) t)).card :=
            agree_restrict_eq Z _ _
        _ ≤ (agreeSet ((e i) : Fin n → F) ((e j) : Fin n → F)).card :=
            filter_card_le_agreeSet_card Z _ _
        _ ≤ k - 1 := rsCode_pairwise_agreeSet_card_le dom hk hci hcj hne
    -- Johnson cap on the punctured block
    refine CodeGeometry.card_le_of_johnson_sq (ι := ↥Z) (α := F) hq1
      (by rw [hcardZ]; exact hz) hL f c ℓ hA hB ?_ ?_
    · rw [hcardZ]; exact hP
    · rw [hcardZ]; exact hsq

/-! ### 3. Uniform packaging: the named `PuncturedListBudget` object -/

open Classical in
/-- **Uniform within-Johnson discharge of `PuncturedListBudget`.**  If on every non-support-
eligible (`a ≤ z`), zero-direction-safe line the punctured squared Johnson condition holds at
level `ℓ`, then the direct punctured-list budget holds with `B = ℓ`.  Non-support-eligibility
supplies the zero-set nonemptiness (`0 < a ≤ z`).  This is exactly the object
`_LowProfileFiberCoupled.lean` §6 names as the surviving sub-`q` route. -/
theorem puncturedListBudget_of_johnson
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a ℓ : ℕ) (ha : 0 < a)
    (hq1 : 1 < Fintype.card F)
    (hwindow : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
        (((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)
            ≤ ((a - (directionSupportSet u₁).card : ℕ) : ℝ))
        ∧ ((ℓ : ℝ) + 1)
            * (((a - (directionSupportSet u₁).card : ℕ) : ℝ)
                - ((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)) ^ 2
          > (((directionZeroSet u₁).card : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((directionZeroSet u₁).card : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
                + (ℓ : ℝ) * (((k - 1 : ℕ) : ℝ)
                    - ((directionZeroSet u₁).card : ℝ) / (Fintype.card F : ℝ)))) :
    PuncturedListBudget dom k a ℓ := by
  intro u₀ u₁ hne hsafe
  have hz : 0 < (directionZeroSet u₁).card := by
    have : a ≤ (directionZeroSet u₁).card := by
      rw [SupportEligibleLineDirection, not_lt] at hne
      exact hne
    omega
  obtain ⟨hP, hsq⟩ := hwindow u₀ u₁ hne hsafe
  exact lineAppearingCodewords_card_le_of_punctured_johnson dom hk a u₀ u₁ hq1 hz ℓ hP hsq

/-! ### 4. Numeric sanity: the squared Johnson condition is satisfiable -/

/-- Sanity: at punctured parameters `z = 4`, `q = 5`, center agreement `A = 3`, pairwise
agreement `B = k − 1 = 1`, the squared Johnson condition holds with list level `ℓ = 2`
(`3·(3 − 4/5)² = 14.52 > 3.2·(3.2 + 2·(1 − 4/5)) = 11.52`).  So the per-line theorem is
non-vacuously applicable. -/
theorem johnson_condition_sanity :
    ((2 : ℝ) + 1) * (((3 : ℕ) : ℝ) - (4 : ℝ) / 5) ^ 2
      > ((4 : ℝ) * (1 - 1 / 5))
        * ((4 : ℝ) * (1 - 1 / 5) + (2 : ℝ) * (((1 : ℕ) : ℝ) - (4 : ℝ) / 5)) := by
  norm_num

end ProximityGap.PuncturedJohnsonDischarge

#print axioms ProximityGap.PuncturedJohnsonDischarge.agree_restrict_eq
#print axioms ProximityGap.PuncturedJohnsonDischarge.filter_card_le_agreeSet_card
#print axioms
  ProximityGap.PuncturedJohnsonDischarge.lineAppearingCodewords_card_le_of_punctured_johnson
#print axioms ProximityGap.PuncturedJohnsonDischarge.puncturedListBudget_of_johnson
#print axioms ProximityGap.PuncturedJohnsonDischarge.johnson_condition_sanity
