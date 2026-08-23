/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Multi-test tail bounds do not amplify without decorrelation

Issue #464 has many distributional routes where one tries several tests, smoothings, projections, or
probes and hopes the common exceptional set shrinks.  This file records the finite obstruction:
individual tail bounds for many tests do not imply product-rate decay for their common exceptional
set unless one proves a decorrelation/transversality theorem.

The aligned singleton model is the sharp obstruction.  Every test has the same one bad atom.  Each
individual tail has mass `1 / #α`, and the common tail also has mass `1 / #α`, not `(1 / #α)^t`.
Thus a multi-test certificate becomes worst-case only at the same one-atom scale as a single test,
unless additional structure proves the bad sets cannot align.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.MultiTestNoAmplification

variable {α ι : Type} [Fintype α]

/-- Tail count for one test. -/
noncomputable def testTailCount (Bad : ι -> α -> Prop) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : α => Bad i a)).card

/-- Empirical tail mass for one test. -/
noncomputable def testTailMass (Bad : ι -> α -> Prop) (i : ι) : ℝ :=
  (testTailCount Bad i : ℝ) / (Fintype.card α : ℝ)

/-- Count of atoms that are bad for every test. -/
noncomputable def jointTailCount (Bad : ι -> α -> Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : α => ∀ i : ι, Bad i a)).card

/-- Empirical mass of atoms bad for every test. -/
noncomputable def jointTailMass (Bad : ι -> α -> Prop) : ℝ :=
  (jointTailCount Bad : ℝ) / (Fintype.card α : ℝ)

/-- The common tail is contained in every individual test tail. -/
theorem jointTailCount_le_testTailCount (Bad : ι -> α -> Prop) (i : ι) :
    jointTailCount Bad ≤ testTailCount Bad i := by
  classical
  unfold jointTailCount testTailCount
  refine Finset.card_le_card ?_
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2 i⟩

/-- Mass form of `jointTailCount_le_testTailCount`. -/
theorem jointTailMass_le_testTailMass (Bad : ι -> α -> Prop) (i : ι) :
    jointTailMass Bad ≤ testTailMass Bad i := by
  have hcount : (jointTailCount Bad : ℝ) ≤ (testTailCount Bad i : ℝ) := by
    exact_mod_cast jointTailCount_le_testTailCount Bad i
  unfold jointTailMass testTailMass
  exact div_le_div_of_nonneg_right hcount (by positivity)

/-- A nonempty common tail has count at least one. -/
theorem one_le_jointTailCount_of_exists
    {Bad : ι -> α -> Prop} (hbad : ∃ a : α, ∀ i : ι, Bad i a) :
    1 ≤ jointTailCount Bad := by
  classical
  rcases hbad with ⟨a, ha⟩
  unfold jointTailCount
  exact Finset.one_le_card.mpr ⟨a, by simp [ha]⟩

/-- A nonempty common tail has mass at least one atom. -/
theorem inv_card_le_jointTailMass_of_exists
    {Bad : ι -> α -> Prop} (hbad : ∃ a : α, ∀ i : ι, Bad i a) :
    (1 : ℝ) / (Fintype.card α : ℝ) ≤ jointTailMass Bad := by
  rcases hbad with ⟨a, ha⟩
  have hden_nonneg : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
  have hcount : (1 : ℝ) ≤ (jointTailCount Bad : ℝ) := by
    exact_mod_cast (one_le_jointTailCount_of_exists (Bad := Bad) ⟨a, ha⟩)
  unfold jointTailMass
  exact div_le_div_of_nonneg_right hcount hden_nonneg

/-- A common-tail mass bound below one atom rules out atoms bad for every test. -/
theorem forall_not_joint_of_jointTailMass_lt_inv_card
    {Bad : ι -> α -> Prop}
    (hsmall : jointTailMass Bad < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ ∀ i : ι, Bad i a := by
  by_contra hnot
  rcases not_forall.mp hnot with ⟨a, hnot_bad⟩
  have hbad : ∃ a : α, ∀ i : ι, Bad i a := ⟨a, Classical.not_not.mp hnot_bad⟩
  exact (not_lt_of_ge (inv_card_le_jointTailMass_of_exists (Bad := Bad) hbad)) hsmall

/-- Individual test tail bounds below one atom rule out a common bad atom, but only because one
chosen individual tail is already below one atom. -/
theorem forall_not_joint_of_individualTailMass_bound_lt_inv_card [Nonempty ι]
    {Bad : ι -> α -> Prop} {U : ℝ}
    (hmass : ∀ i : ι, testTailMass Bad i ≤ U)
    (hU : U < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ ∀ i : ι, Bad i a := by
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  have hjoint : jointTailMass Bad < (1 : ℝ) / (Fintype.card α : ℝ) :=
    lt_of_le_of_lt (le_trans (jointTailMass_le_testTailMass Bad i₀) (hmass i₀)) hU
  exact forall_not_joint_of_jointTailMass_lt_inv_card (Bad := Bad) hjoint

/-- In the aligned singleton model, every individual test tail has count one. -/
theorem testTailCount_aligned_singleton (a₀ : α) (i : ι) :
    testTailCount (fun _i : ι => fun a : α => a = a₀) i = 1 := by
  classical
  unfold testTailCount
  convert Finset.card_singleton a₀
  ext a
  simp

/-- In the aligned singleton model, every individual test tail has mass one atom. -/
theorem testTailMass_aligned_singleton (a₀ : α) (i : ι) :
    testTailMass (fun _i : ι => fun a : α => a = a₀) i
      = (1 : ℝ) / (Fintype.card α : ℝ) := by
  simp [testTailMass, testTailCount_aligned_singleton a₀ i]

/-- With at least one test, the common tail of the aligned singleton model has count one. -/
theorem jointTailCount_aligned_singleton [Nonempty ι] (a₀ : α) :
    jointTailCount (fun _i : ι => fun a : α => a = a₀) = 1 := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  unfold jointTailCount
  convert Finset.card_singleton a₀
  ext a
  constructor
  · intro ha
    have hall : ∀ _i : ι, a = a₀ := by simpa using ha
    simpa using hall i₀
  · intro ha
    simp at ha
    simp [ha]

/-- The common tail of the aligned singleton model has mass one atom, not a product of the
individual masses. -/
theorem jointTailMass_aligned_singleton [Nonempty ι] (a₀ : α) :
    jointTailMass (fun _i : ι => fun a : α => a = a₀)
      = (1 : ℝ) / (Fintype.card α : ℝ) := by
  simp [jointTailMass, jointTailCount_aligned_singleton a₀]

/-- Any individual tail budget at least one atom admits a common bad atom for all tests. -/
theorem individual_budget_allows_common_spike [Nonempty α] [Nonempty ι]
    {U : ℝ} (hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U) :
    ∃ Bad : ι -> α -> Prop,
      (∀ i : ι, testTailMass Bad i ≤ U) ∧
      ∃ a : α, ∀ i : ι, Bad i a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨fun _i : ι => fun a : α => a = a₀, ?_, ⟨a₀, ?_⟩⟩
  · intro i
    simpa [testTailMass_aligned_singleton a₀ i] using hU
  · intro i
    rfl

/-- Exact atom-scale gate for converting many individual test bounds into absence of a common bad
atom.  Repeating tests gives no product-rate gain unless extra decorrelation is supplied. -/
theorem atomScaleGate_for_multiTest_common_bad
    [Nonempty α] [Nonempty ι] {U : ℝ} :
    (∀ Bad : ι -> α -> Prop,
        (∀ i : ι, testTailMass Bad i ≤ U) ->
        ∀ a : α, ¬ ∀ i : ι, Bad i a)
      ↔ U < (1 : ℝ) / (Fintype.card α : ℝ) := by
  constructor
  · intro h
    by_contra hnot
    have hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U := le_of_not_gt hnot
    rcases individual_budget_allows_common_spike (α := α) (ι := ι) hU with
      ⟨Bad, hmass, a, ha⟩
    exact (h Bad hmass a) ha
  · intro hU Bad hmass
    exact forall_not_joint_of_individualTailMass_bound_lt_inv_card
      (Bad := Bad) hmass hU

#print axioms jointTailCount_le_testTailCount
#print axioms jointTailMass_le_testTailMass
#print axioms one_le_jointTailCount_of_exists
#print axioms inv_card_le_jointTailMass_of_exists
#print axioms forall_not_joint_of_jointTailMass_lt_inv_card
#print axioms forall_not_joint_of_individualTailMass_bound_lt_inv_card
#print axioms testTailCount_aligned_singleton
#print axioms testTailMass_aligned_singleton
#print axioms jointTailCount_aligned_singleton
#print axioms jointTailMass_aligned_singleton
#print axioms individual_budget_allows_common_spike
#print axioms atomScaleGate_for_multiTest_common_bad

end ArkLib.ProximityGap.Frontier.MultiTestNoAmplification
