/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Atom-scale barrier for Wasserstein/equidistribution attacks

Quantitative equidistribution results, including Wasserstein-distance statements, are distributional
inputs.  To prove the proximity-gap floor from such an input one must exclude even a single bad
frequency / stack / coset representative.  For an empirical distribution on `N` atoms, one bad atom
has mass exactly `1/N`.

This file records the finite counting fact behind that obstruction.  Any tail-mass upper bound
`U` rules out all bad atoms only when `U < 1/N`.  If `1/N <= U`, a one-atom spike is still consistent
with the bound.  In the prize regime `N = (p - 1) / n` is the dilation-quotient size, so a
Wasserstein or discrepancy theorem must reach union-bound scale before it can imply the needed
worst-case Paley / incidence statement.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.WassersteinAtomScaleBarrier

variable {α : Type} [Fintype α]

/-- Number of empirical atoms satisfying the tail predicate `Bad`. -/
noncomputable def empiricalTailCount (Bad : α -> Prop) : ℕ := by
  classical
  exact (Finset.univ.filter Bad).card

/-- Empirical mass of the tail predicate `Bad`, with each atom weighted uniformly. -/
noncomputable def empiricalTailMass (Bad : α -> Prop) : ℝ :=
  (empiricalTailCount Bad : ℝ) / (Fintype.card α : ℝ)

/-- A tail has zero empirical count exactly when no atom satisfies the predicate. -/
theorem empiricalTailCount_eq_zero_iff_forall_not
    (Bad : α -> Prop) :
    empiricalTailCount Bad = 0 ↔ ∀ a : α, ¬ Bad a := by
  classical
  unfold empiricalTailCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

/-- A nonempty tail has empirical count at least one. -/
theorem one_le_empiricalTailCount_of_exists
    {Bad : α -> Prop} (hbad : ∃ a : α, Bad a) :
    1 ≤ empiricalTailCount Bad := by
  classical
  rcases hbad with ⟨a, ha⟩
  unfold empiricalTailCount
  exact Finset.one_le_card.mpr ⟨a, by simp [ha]⟩

/-- A nonempty empirical tail has mass at least the mass of one atom, `1 / #α`. -/
theorem inv_card_le_empiricalTailMass_of_exists
    {Bad : α -> Prop} (hbad : ∃ a : α, Bad a) :
    (1 : ℝ) / (Fintype.card α : ℝ) ≤ empiricalTailMass Bad := by
  classical
  rcases hbad with ⟨a, ha⟩
  have hden_nonneg : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
  have hcount : (1 : ℝ) ≤ (empiricalTailCount Bad : ℝ) := by
    exact_mod_cast (one_le_empiricalTailCount_of_exists (Bad := Bad) ⟨a, ha⟩)
  unfold empiricalTailMass
  exact div_le_div_of_nonneg_right hcount hden_nonneg

/-- A tail-mass bound below one atom forces the tail to be empty. -/
theorem forall_not_of_empiricalTailMass_lt_inv_card
    {Bad : α -> Prop}
    (hsmall : empiricalTailMass Bad < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ Bad a := by
  classical
  by_contra hnot
  rcases not_forall.mp hnot with ⟨a, hnot_bad⟩
  have hbad : ∃ a : α, Bad a := ⟨a, Classical.not_not.mp hnot_bad⟩
  exact (not_lt_of_ge (inv_card_le_empiricalTailMass_of_exists (Bad := Bad) hbad)) hsmall

/-- Singleton tail predicates have empirical count exactly one. -/
theorem empiricalTailCount_singleton [DecidableEq α] (a₀ : α) :
    empiricalTailCount (fun a : α => a = a₀) = 1 := by
  classical
  unfold empiricalTailCount
  convert Finset.card_singleton a₀
  ext a
  simp

/-- Singleton tail predicates have empirical mass exactly `1 / #α`. -/
theorem empiricalTailMass_singleton [DecidableEq α] (a₀ : α) :
    empiricalTailMass (fun a : α => a = a₀)
      = (1 : ℝ) / (Fintype.card α : ℝ) := by
  classical
  simp [empiricalTailMass, empiricalTailCount_singleton]

/-- Any count budget allowing one atom is consistent with a nonempty tail. -/
theorem count_budget_allows_single_spike [Nonempty α] [DecidableEq α]
    {B : ℕ} (hB : 1 ≤ B) :
    ∃ Bad : α -> Prop, empiricalTailCount Bad ≤ B ∧ ∃ a : α, Bad a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨fun a : α => a = a₀, ?_, ⟨a₀, rfl⟩⟩
  simpa [empiricalTailCount_singleton] using hB

/-- Any tail-mass budget at least the one-atom mass is consistent with a nonempty tail. -/
theorem mass_budget_allows_single_spike [Nonempty α] [DecidableEq α]
    {U : ℝ} (hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U) :
    ∃ Bad : α -> Prop, empiricalTailMass Bad ≤ U ∧ ∃ a : α, Bad a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨fun a : α => a = a₀, ?_, ⟨a₀, rfl⟩⟩
  simpa [empiricalTailMass_singleton] using hU

/-- Real-valued distributional tail estimates exclude all bad atoms only if their bound beats the
one-atom scale.  This is the abstract gate a Wasserstein/smoothed-discrepancy proof must pass. -/
theorem atomScaleGate_for_distributional_tail_bound [Nonempty α] [DecidableEq α]
    {U : ℝ} :
    (∀ Bad : α -> Prop, empiricalTailMass Bad ≤ U -> ∀ a : α, ¬ Bad a)
      ↔ U < (1 : ℝ) / (Fintype.card α : ℝ) := by
  constructor
  · intro h
    by_contra hnot
    have hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U := le_of_not_gt hnot
    rcases mass_budget_allows_single_spike (α := α) hU with ⟨Bad, hmass, a, ha⟩
    exact (h Bad hmass a) ha
  · intro hsmall Bad hmass
    exact forall_not_of_empiricalTailMass_lt_inv_card
      (Bad := Bad) (lt_of_le_of_lt hmass hsmall)

#print axioms empiricalTailCount_eq_zero_iff_forall_not
#print axioms one_le_empiricalTailCount_of_exists
#print axioms inv_card_le_empiricalTailMass_of_exists
#print axioms forall_not_of_empiricalTailMass_lt_inv_card
#print axioms empiricalTailCount_singleton
#print axioms empiricalTailMass_singleton
#print axioms count_budget_allows_single_spike
#print axioms mass_budget_allows_single_spike
#print axioms atomScaleGate_for_distributional_tail_bound

end ArkLib.ProximityGap.Frontier.WassersteinAtomScaleBarrier
