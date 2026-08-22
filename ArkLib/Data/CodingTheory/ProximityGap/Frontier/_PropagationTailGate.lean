/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Propagation is the only way distributional tails beat one-atom scale

`_VerticalTailSupConsumer`, `_QuotientTailSupConsumer`, and
`_WassersteinAtomScaleBarrier` record the one-atom obstruction for issue #464: a tail estimate on a
finite quotient becomes a worst-case/sup estimate only below the mass of one atom.

This file isolates the only finite escape hatch.  If every bad atom forces a whole propagated cluster
of at least `s` bad atoms, then a distributional tail estimate below `s / #atoms` is enough.  The new
mathematical burden is exactly the anti-spike theorem:

* prove a relation/propagation mechanism forcing `s` bad quotient atoms from one bad quotient atom;
* or exhibit a singleton/small-cluster bad tail, which refutes that mechanism.

The Lean content here is deliberately finite and method-agnostic.  It does **not** assert that Gauss
periods, Paley spectra, or Door-IV incidences have such propagation; it states the gate any proposed
anti-spike route must pass.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.PropagationTailGate

variable {α : Type} [Fintype α]

/-- Number of atoms satisfying a bad-tail predicate. -/
noncomputable def badCount (Bad : α -> Prop) : ℕ := by
  classical
  exact (Finset.univ.filter Bad).card

/-- Uniform empirical mass of a bad-tail predicate. -/
noncomputable def badMass (Bad : α -> Prop) : ℝ :=
  (badCount Bad : ℝ) / (Fintype.card α : ℝ)

/-- The anti-spike/minimum-support hypothesis: any nonempty bad tail has at least `s` atoms. -/
def MinimumBadTailCard (Bad : α -> Prop) (s : ℕ) : Prop :=
  (∃ a : α, Bad a) -> s ≤ badCount Bad

/-- Bad atoms reachable from `a` along a proposed propagation relation `R`. -/
noncomputable def badNeighborhoodCount (R : α -> α -> Prop) (Bad : α -> Prop) (a : α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun b : α => R a b ∧ Bad b)).card

/-- Relation-level anti-spike hypothesis: every bad atom has at least `s` bad propagated neighbors. -/
def BadPropagates (R : α -> α -> Prop) (Bad : α -> Prop) (s : ℕ) : Prop :=
  ∀ a : α, Bad a -> s ≤ badNeighborhoodCount R Bad a

/-- A propagated bad neighborhood is contained in the whole bad tail. -/
theorem badNeighborhoodCount_le_badCount
    (R : α -> α -> Prop) (Bad : α -> Prop) (a : α) :
    badNeighborhoodCount R Bad a ≤ badCount Bad := by
  classical
  unfold badNeighborhoodCount badCount
  refine Finset.card_le_card ?_
  intro b hb
  rw [Finset.mem_filter] at hb ⊢
  exact ⟨hb.1, hb.2.2⟩

/-- A relation-level propagation lower bound implies the abstract minimum-tail-cardinality
hypothesis. -/
theorem minimumBadTailCard_of_badPropagates
    {R : α -> α -> Prop} {Bad : α -> Prop} {s : ℕ}
    (hprop : BadPropagates R Bad s) :
    MinimumBadTailCard Bad s := by
  intro hbad
  rcases hbad with ⟨a, ha⟩
  exact le_trans (hprop a ha) (badNeighborhoodCount_le_badCount R Bad a)

/-- Count form of the propagation gate: if every nonempty bad tail has at least `s` atoms, a count
bound below `s` rules out all bad atoms. -/
theorem forall_not_of_badCount_lt_minimumCard
    {Bad : α -> Prop} {s : ℕ}
    (hmin : MinimumBadTailCard Bad s)
    (hsmall : badCount Bad < s) :
    ∀ a : α, ¬ Bad a := by
  intro a ha
  exact (not_lt_of_ge (hmin ⟨a, ha⟩)) hsmall

/-- Relation-level count gate: propagation plus a count bound below the propagated cluster size
rules out all bad atoms. -/
theorem forall_not_of_badPropagates_badCount_lt
    {R : α -> α -> Prop} {Bad : α -> Prop} {s : ℕ}
    (hprop : BadPropagates R Bad s)
    (hsmall : badCount Bad < s) :
    ∀ a : α, ¬ Bad a :=
  forall_not_of_badCount_lt_minimumCard
    (Bad := Bad) (s := s) (minimumBadTailCard_of_badPropagates hprop) hsmall

/-- Mass form of the propagation gate: a tail-mass estimate below `s / #α` rules out all bad atoms
once every nonempty bad tail has at least `s` atoms. -/
theorem forall_not_of_badMass_lt_minimumScale
    {Bad : α -> Prop} {s : ℕ}
    (hmin : MinimumBadTailCard Bad s)
    (hsmall : badMass Bad < (s : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ Bad a := by
  intro a ha
  have hden_nonneg : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
  have hcount : (s : ℝ) ≤ (badCount Bad : ℝ) := by
    exact_mod_cast (hmin ⟨a, ha⟩)
  have hmass_ge : (s : ℝ) / (Fintype.card α : ℝ) ≤ badMass Bad := by
    unfold badMass
    exact div_le_div_of_nonneg_right hcount hden_nonneg
  exact (not_lt_of_ge hmass_ge) hsmall

/-- If a proven distributional upper bound is below the propagation scale `s / #α`, it gives a
worst-case exclusion under the minimum-tail-cardinality hypothesis. -/
theorem forall_not_of_badMass_bound_lt_minimumScale
    {Bad : α -> Prop} {s : ℕ} {U : ℝ}
    (hmin : MinimumBadTailCard Bad s)
    (hmass : badMass Bad ≤ U)
    (hU : U < (s : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ Bad a :=
  forall_not_of_badMass_lt_minimumScale
    (Bad := Bad) (s := s) hmin (lt_of_le_of_lt hmass hU)

/-- Relation-level mass gate: if one bad atom propagates to at least `s` bad atoms, a mass bound
below `s / #α` is enough for a worst-case exclusion. -/
theorem forall_not_of_badPropagates_badMass_bound_lt_scale
    {R : α -> α -> Prop} {Bad : α -> Prop} {s : ℕ} {U : ℝ}
    (hprop : BadPropagates R Bad s)
    (hmass : badMass Bad ≤ U)
    (hU : U < (s : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, ¬ Bad a :=
  forall_not_of_badMass_bound_lt_minimumScale
    (Bad := Bad) (s := s) (minimumBadTailCard_of_badPropagates hprop) hmass hU

/-- Refutation API: a bad atom together with a tail count below `s` disproves the proposed
minimum-tail-cardinality/anti-spike theorem. -/
theorem not_minimumBadTailCard_of_exists_badCount_lt
    {Bad : α -> Prop} {s : ℕ}
    (hbad : ∃ a : α, Bad a)
    (hsmall : badCount Bad < s) :
    ¬ MinimumBadTailCard Bad s := by
  intro hmin
  exact (not_lt_of_ge (hmin hbad)) hsmall

/-- Refutation API for relation-level propagation: one bad atom with too few bad propagated
neighbors disproves `BadPropagates`. -/
theorem not_badPropagates_of_badNeighborhoodCount_lt
    {R : α -> α -> Prop} {Bad : α -> Prop} {s : ℕ} {a : α}
    (ha : Bad a)
    (hsmall : badNeighborhoodCount R Bad a < s) :
    ¬ BadPropagates R Bad s := by
  intro hprop
  exact (not_lt_of_ge (hprop a ha)) hsmall

/-- Tail count for a singleton bad predicate. -/
theorem badCount_singleton (a₀ : α) :
    badCount (fun a : α => a = a₀) = 1 := by
  classical
  unfold badCount
  convert Finset.card_singleton a₀
  ext a
  simp

/-- Tail mass for a singleton bad predicate. -/
theorem badMass_singleton (a₀ : α) :
    badMass (fun a : α => a = a₀) = (1 : ℝ) / (Fintype.card α : ℝ) := by
  simp [badMass, badCount_singleton]

/-- A singleton bad tail refutes any claimed minimum bad-tail size strictly larger than one. -/
theorem singleton_not_minimumBadTailCard_of_one_lt
    (a₀ : α) {s : ℕ} (hs : 1 < s) :
    ¬ MinimumBadTailCard (fun a : α => a = a₀) s := by
  refine not_minimumBadTailCard_of_exists_badCount_lt
    (Bad := fun a : α => a = a₀) (s := s) ⟨a₀, rfl⟩ ?_
  simpa [badCount_singleton] using hs

#print axioms badNeighborhoodCount_le_badCount
#print axioms minimumBadTailCard_of_badPropagates
#print axioms forall_not_of_badCount_lt_minimumCard
#print axioms forall_not_of_badPropagates_badCount_lt
#print axioms forall_not_of_badMass_lt_minimumScale
#print axioms forall_not_of_badMass_bound_lt_minimumScale
#print axioms forall_not_of_badPropagates_badMass_bound_lt_scale
#print axioms not_minimumBadTailCard_of_exists_badCount_lt
#print axioms not_badPropagates_of_badNeighborhoodCount_lt
#print axioms badCount_singleton
#print axioms badMass_singleton
#print axioms singleton_not_minimumBadTailCard_of_one_lt

end ArkLib.ProximityGap.Frontier.PropagationTailGate
