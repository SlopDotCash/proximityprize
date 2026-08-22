/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-!
# Collinear proximates ([BCKHS25] Lemma 2.4)

The distance-restoration lemma from "On Proximity Gaps for Reed–Solomon
Codes" (Ben-Sasson, Carmon, Haböck, Kopparty, Saraf, November 2025): if the
line combinations `u₀ + z·u₁` and `p₀ + z·p₁` are within Hamming distance `e`
for `a ≥ 2` values of `z`, then the joint disagreement set of the PAIRS has
size at most `a/(a−1) · e`. Stated here in the natural-number product form
`(a − 1) · d ≤ a · e` (no division).

This is the final step of the [BCKHS25] §2 Berlekamp–Welch route to
unique-decoding-regime correlated agreement (the oversized error-locator
loses distance; this lemma restores it), and the first formalized brick of
the Hensel-free route to the remaining list-decoding keystones mapped in
remaining-proofs-research.md.
-/

namespace BCKHS25

-- Decidability/Fintype instances are threaded through the section; several
-- statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The joint disagreement set of the pairs `(u₀, u₁)` and `(p₀, p₁)`. -/
private def jointDisagreement (u₀ u₁ p₀ p₁ : ι → F) : Finset ι :=
  Finset.univ.filter (fun x => ¬(u₀ x = p₀ x ∧ u₁ x = p₁ x))

/-- At a joint-disagreement point, at most one `z` can reconcile the line
combinations: the difference is an affine-in-`z` expression with not all
coefficients zero. -/
private lemma card_reconciling_le_one (u₀ u₁ p₀ p₁ : ι → F) {x : ι}
    (hx : x ∈ jointDisagreement u₀ u₁ p₀ p₁) (Z : Finset F) :
    (Z.filter (fun z => u₀ x + z * u₁ x = p₀ x + z * p₁ x)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z₁ hz₁ z₂ hz₂
  have h₁ := (Finset.mem_filter.mp hz₁).2
  have h₂ := (Finset.mem_filter.mp hz₂).2
  simp only [jointDisagreement, Finset.mem_filter, Finset.mem_univ, true_and,
    not_and_or] at hx
  by_contra hne
  -- subtract the two reconciliations: (z₁ − z₂) · (u₁ x − p₁ x) = 0
  have hdiff : (z₁ - z₂) * (u₁ x - p₁ x) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hdiff with h | h
  · exact hne (sub_eq_zero.mp h)
  · -- u₁ x = p₁ x forces u₀ x = p₀ x via h₁, contradicting joint disagreement
    have hu₁ : u₁ x = p₁ x := sub_eq_zero.mp h
    have hu₀ : u₀ x = p₀ x := by
      have h₁' := h₁
      rw [hu₁] at h₁'
      exact add_right_cancel h₁'
    rcases hx with hx | hx
    · exact hx hu₀
    · exact hx hu₁

/-- **[BCKHS25] Lemma 2.4 (collinear proximates), product form.** If
`Δ(u₀ + z·u₁, p₀ + z·p₁) ≤ e` for every `z` in a set `Z` with `|Z| ≥ 2`, then
the joint disagreement count `d` satisfies `(|Z| − 1) · d ≤ |Z| · e`
(equivalently `d ≤ |Z|/(|Z|−1) · e`). -/
theorem card_jointDisagreement_mul_le {u₀ u₁ p₀ p₁ : ι → F} {e : ℕ}
    (Z : Finset F) (_hZ : 2 ≤ Z.card)
    (hclose : ∀ z ∈ Z,
      hammingDist (fun x => u₀ x + z * u₁ x) (fun x => p₀ x + z * p₁ x) ≤ e) :
    (Z.card - 1) * (jointDisagreement u₀ u₁ p₀ p₁).card ≤ Z.card * e := by
  classical
  set E := jointDisagreement u₀ u₁ p₀ p₁ with hE
  set d := E.card with hd
  -- the per-z agreement sets inside E
  set A : F → Finset ι := fun z => E.filter (fun x => u₀ x + z * u₁ x = p₀ x + z * p₁ x)
    with hA
  -- each A z has size ≥ d − e: outside A z (within E) the z-combination disagrees
  have hAcard : ∀ z ∈ Z, d - e ≤ (A z).card := by
    intro z hz
    have hsub : E \ A z ⊆ Finset.univ.filter
        (fun x => (fun x => u₀ x + z * u₁ x) x ≠ (fun x => p₀ x + z * p₁ x) x) := by
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxE, hxA⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro heq
      exact hxA (Finset.mem_filter.mpr ⟨hxE, heq⟩)
    have hdiff_le : (E \ A z).card ≤ e := by
      refine le_trans (Finset.card_le_card hsub) ?_
      simpa [hammingDist] using hclose z hz
    have hsplit : d ≤ (E \ A z).card + (A z).card :=
      Finset.card_le_card_sdiff_add_card
    omega
  -- the A z are pairwise disjoint (a point in two of them would have two reconciling z's)
  have hdisj : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ ≠ z₂ → Disjoint (A z₁) (A z₂) := by
    intro z₁ hz₁ z₂ hz₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hxE : x ∈ E := (Finset.mem_filter.mp hx₁).1
    have hkey := card_reconciling_le_one u₀ u₁ p₀ p₁ (by simpa [hE] using hxE) {z₁, z₂}
    have h2 : ({z₁, z₂} : Finset F).filter
        (fun z => u₀ x + z * u₁ x = p₀ x + z * p₁ x) = {z₁, z₂} := by
      rw [Finset.filter_eq_self]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (Finset.mem_filter.mp hx₁).2
      · rcases Finset.mem_singleton.mp hz with rfl
        exact (Finset.mem_filter.mp hx₂).2
    rw [h2] at hkey
    have : ({z₁, z₂} : Finset F).card = 2 := Finset.card_pair hne
    omega
  -- sum the disjoint agreement sets inside E
  have hsum : ∑ z ∈ Z, (A z).card ≤ d := by
    have hunion : (Z.biUnion A) ⊆ E := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨z, _, hxz⟩
      exact (Finset.mem_filter.mp hxz).1
    calc ∑ z ∈ Z, (A z).card
        = (Z.biUnion A).card := (Finset.card_biUnion hdisj).symm
      _ ≤ d := Finset.card_le_card hunion
  -- combine: |Z|·(d − e) ≤ Σ |A z| ≤ d, then rearrange in ℕ
  have hlower : Z.card * (d - e) ≤ ∑ z ∈ Z, (A z).card := by
    calc Z.card * (d - e) = ∑ _z ∈ Z, (d - e) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ z ∈ Z, (A z).card := Finset.sum_le_sum hAcard
  have hmain : Z.card * (d - e) ≤ d := le_trans hlower hsum
  -- case on d ≤ e (trivial) vs e < d (arithmetic)
  by_cases hde : d ≤ e
  · calc (Z.card - 1) * d ≤ Z.card * d := Nat.mul_le_mul_right d (Nat.sub_le _ _)
      _ ≤ Z.card * e := Nat.mul_le_mul_left _ hde
  · push Not at hde
    -- distribute, then rearrange with sub_le_iff (products are opaque to omega)
    have hms : Z.card * (d - e) = Z.card * d - Z.card * e := by
      rw [Nat.mul_comm, Nat.sub_mul, Nat.mul_comm d, Nat.mul_comm e]
    have h1 : Z.card * d - Z.card * e ≤ d := hms ▸ hmain
    have h2 : Z.card * d ≤ d + Z.card * e := Nat.sub_le_iff_le_add.mp h1
    calc (Z.card - 1) * d = Z.card * d - d := by rw [Nat.sub_mul, one_mul]
      _ ≤ Z.card * e := Nat.sub_le_iff_le_add'.mpr h2

/-- **[BCKHS25] Lemma 2.4 (collinear proximates), public filter form.** Same as
`card_jointDisagreement_mul_le` but with the joint disagreement count exposed as
an explicit `Finset.filter` cardinality (the private `jointDisagreement` def is
not nameable downstream). This is the form consumed by the §2 distance
restoration after the joint proximate of Claim 2.3. -/
theorem card_jointDisagreement_filter_mul_le {u₀ u₁ p₀ p₁ : ι → F} {e : ℕ}
    (Z : Finset F) (hZ : 2 ≤ Z.card)
    (hclose : ∀ z ∈ Z,
      hammingDist (fun x => u₀ x + z * u₁ x) (fun x => p₀ x + z * p₁ x) ≤ e) :
    (Z.card - 1) *
        (Finset.univ.filter (fun x => ¬(u₀ x = p₀ x ∧ u₁ x = p₁ x))).card
      ≤ Z.card * e :=
  card_jointDisagreement_mul_le Z hZ hclose

end BCKHS25
