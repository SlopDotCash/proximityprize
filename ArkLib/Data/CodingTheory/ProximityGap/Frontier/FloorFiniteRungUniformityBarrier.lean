/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite floor rungs do not prove uniform localization

The off-BGK floor lane has two verified rungs:

* `a = 4`, `n = 16`, floor-bad prime `{17}`;
* `a = 5`, `n = 32`, floor-bad prime `{97}`.

Both match the proposed rule "floor-bad equals the least prime `1 mod 2^a`".  The prize-facing
input, however, is a uniform statement for every `a >= 4`.  This file records the purely logical
barrier: finite rung evidence cannot imply that uniform statement without an additional structural
propagation theorem.

It also records the positive shape of such a theorem: a base rung plus a successor step
`R a -> R (a+1)` does give uniformity.  For the floor lane, that successor step would be the real
new mathematics: a tower/renormalization proof that the least-prime characterization propagates.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier

/-- A predicate `R` has been verified on the finite set of rungs `S`. -/
def VerifiedOn (S : Finset ℕ) (R : ℕ -> Prop) : Prop :=
  ∀ a : ℕ, a ∈ S -> R a

/-- A predicate `R` has been verified on every rung in the interval `[start, cutoff]`. -/
def VerifiedPrefix (start cutoff : ℕ) (R : ℕ -> Prop) : Prop :=
  ∀ a : ℕ, start ≤ a -> a ≤ cutoff -> R a

/-- The uniform statement needed by the floor-localization lane. -/
def UniformFrom (start : ℕ) (R : ℕ -> Prop) : Prop :=
  ∀ a : ℕ, start ≤ a -> R a

/-- A successor propagation theorem for a predicate from a starting rung onward. -/
def SuccessorStep (start : ℕ) (R : ℕ -> Prop) : Prop :=
  ∀ a : ℕ, start ≤ a -> R a -> R (a + 1)

/-- Verification on the interval finset is exactly prefix verification. -/
theorem verifiedOn_Icc_iff_verifiedPrefix
    (start cutoff : ℕ) (R : ℕ -> Prop) :
    VerifiedOn (Finset.Icc start cutoff) R ↔ VerifiedPrefix start cutoff R := by
  constructor
  · intro h a hstart hcutoff
    exact h a (Finset.mem_Icc.mpr ⟨hstart, hcutoff⟩)
  · intro h a ha
    exact h a (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2

/-- Finite verification on `S` cannot force uniformity past an unverified future rung. -/
theorem verifiedOn_not_force_uniform
    (S : Finset ℕ) {start future : ℕ}
    (hfuture : start ≤ future) (hnot : future ∉ S) :
    ¬ (∀ R : ℕ -> Prop, VerifiedOn S R -> UniformFrom start R) := by
  intro h
  let R : ℕ -> Prop := fun a => a ∈ S
  have hverified : VerifiedOn S R := by
    intro a ha
    exact ha
  have huniform : UniformFrom start R := h R hverified
  exact hnot (huniform future hfuture)

/-- The interval model that agrees with every checked prefix rung and fails immediately after it. -/
def PrefixModel (cutoff : ℕ) : ℕ -> Prop :=
  fun a => a ≤ cutoff

/-- `PrefixModel cutoff` verifies every requested rung up to `cutoff`. -/
theorem prefixModel_verifiedPrefix (start cutoff : ℕ) :
    VerifiedPrefix start cutoff (PrefixModel cutoff) := by
  intro a _hstart hacutoff
  exact hacutoff

/-- A checked prefix cannot force uniformity at the next rung. -/
theorem verifiedPrefix_not_force_uniform {start cutoff : ℕ}
    (hnext : start ≤ cutoff + 1) :
    ¬ (∀ R : ℕ -> Prop, VerifiedPrefix start cutoff R -> UniformFrom start R) := by
  intro h
  have hverified : VerifiedPrefix start cutoff (PrefixModel cutoff) :=
    prefixModel_verifiedPrefix start cutoff
  have huniform : UniformFrom start (PrefixModel cutoff) := h (PrefixModel cutoff) hverified
  have hbad : cutoff + 1 ≤ cutoff := huniform (cutoff + 1) hnext
  exact (Nat.not_succ_le_self cutoff) hbad

/-- The concrete `a = 4, 5` floor evidence, by itself, does not force uniformity for all `a >= 4`.
-/
theorem two_rung_floor_evidence_not_uniform :
    ¬ (∀ R : ℕ -> Prop, VerifiedPrefix 4 5 R -> UniformFrom 4 R) :=
  verifiedPrefix_not_force_uniform (start := 4) (cutoff := 5) (by decide)

/-- The same concrete guardrail phrased as finite-set evidence on the checked interval
`{4, 5}`. -/
theorem two_rung_floor_interval_evidence_not_uniform :
    ¬ (∀ R : ℕ -> Prop, VerifiedOn (Finset.Icc 4 5) R -> UniformFrom 4 R) := by
  intro h
  exact two_rung_floor_evidence_not_uniform
    (fun R hprefix =>
      h R ((verifiedOn_Icc_iff_verifiedPrefix 4 5 R).mpr hprefix))

/-- Uniformity fails exactly when some rung at or after `start` fails. -/
theorem not_uniformFrom_iff_exists_failure
    (start : ℕ) (R : ℕ -> Prop) :
    (¬ UniformFrom start R) ↔ ∃ a : ℕ, start ≤ a ∧ ¬ R a := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro a ha
    by_contra hfail
    exact hnone ⟨a, ha, hfail⟩
  · rintro ⟨a, ha, hfail⟩ huniform
    exact hfail (huniform a ha)

/-- A successor theorem fails exactly when some verified rung does not propagate to the next
rung. -/
theorem not_successorStep_iff_exists_next_failure
    (start : ℕ) (R : ℕ -> Prop) :
    (¬ SuccessorStep start R) ↔ ∃ a : ℕ, start ≤ a ∧ R a ∧ ¬ R (a + 1) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro a ha hR
    by_contra hnext
    exact hnone ⟨a, ha, hR, hnext⟩
  · rintro ⟨a, ha, hR, hnext⟩ hstep
    exact hnext (hstep a ha hR)

/-- Positive replacement: a base rung plus a successor propagation theorem proves uniformity. -/
theorem uniformFrom_of_base_and_successor_step
    {R : ℕ -> Prop} {start : ℕ}
    (hbase : R start)
    (hstep : ∀ a : ℕ, start ≤ a -> R a -> R (a + 1)) :
    UniformFrom start R := by
  intro a ha
  exact Nat.le_induction hbase (fun n hn ih => hstep n hn ih) a ha

/-- A verified prefix plus a global successor step proves uniformity.  The floor lane currently has
the verified prefix; the missing mathematical input is the successor step. -/
theorem uniformFrom_of_verifiedPrefix_and_successor_step
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hprefix : VerifiedPrefix start cutoff R)
    (hstep : ∀ a : ℕ, start ≤ a -> R a -> R (a + 1)) :
    UniformFrom start R :=
  uniformFrom_of_base_and_successor_step
    (R := R) (start := start) (hprefix start le_rfl hsc) hstep

/-- Positive replacement stated with the named successor-step predicate. -/
theorem uniformFrom_of_base_and_successorStep
    {R : ℕ -> Prop} {start : ℕ}
    (hbase : R start)
    (hstep : SuccessorStep start R) :
    UniformFrom start R :=
  uniformFrom_of_base_and_successor_step hbase hstep

/-- Prefix version stated with the named successor-step predicate. -/
theorem uniformFrom_of_verifiedPrefix_and_successorStep
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hprefix : VerifiedPrefix start cutoff R)
    (hstep : SuccessorStep start R) :
    UniformFrom start R :=
  uniformFrom_of_verifiedPrefix_and_successor_step hsc hprefix hstep

/-- Interval-finset version of the positive replacement: verified interval evidence plus a
successor step proves uniformity. -/
theorem uniformFrom_of_verifiedOn_Icc_and_successorStep
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc start cutoff) R)
    (hstep : SuccessorStep start R) :
    UniformFrom start R :=
  uniformFrom_of_verifiedPrefix_and_successorStep hsc
    ((verifiedOn_Icc_iff_verifiedPrefix start cutoff R).mp hverified) hstep

/-- Once a prefix has been verified, any failure of uniformity refutes the successor step. -/
theorem not_successorStep_of_verifiedPrefix_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hprefix : VerifiedPrefix start cutoff R)
    (hnot : ¬ UniformFrom start R) :
    ¬ SuccessorStep start R := by
  intro hstep
  exact hnot (uniformFrom_of_verifiedPrefix_and_successorStep hsc hprefix hstep)

/-- Interval-finset version: checked interval evidence plus failed uniformity forces the successor
step itself to fail. -/
theorem not_successorStep_of_verifiedOn_Icc_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc start cutoff) R)
    (hnot : ¬ UniformFrom start R) :
    ¬ SuccessorStep start R :=
  not_successorStep_of_verifiedPrefix_of_not_uniformFrom hsc
    ((verifiedOn_Icc_iff_verifiedPrefix start cutoff R).mp hverified) hnot

/-- Scanner form: if a verified prefix does not extend to uniformity, some verified rung fails to
propagate to its successor. -/
theorem exists_next_failure_of_verifiedPrefix_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hprefix : VerifiedPrefix start cutoff R)
    (hnot : ¬ UniformFrom start R) :
    ∃ a : ℕ, start ≤ a ∧ R a ∧ ¬ R (a + 1) :=
  (not_successorStep_iff_exists_next_failure start R).mp
    (not_successorStep_of_verifiedPrefix_of_not_uniformFrom hsc hprefix hnot)

/-- A prefix scanner can place the first adjacent successor failure at or beyond the checked
cutoff: a failure below the cutoff would contradict prefix verification at `a + 1`. -/
theorem exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hprefix : VerifiedPrefix start cutoff R)
    (hnot : ¬ UniformFrom start R) :
    ∃ a : ℕ, cutoff ≤ a ∧ start ≤ a ∧ R a ∧ ¬ R (a + 1) := by
  rcases exists_next_failure_of_verifiedPrefix_of_not_uniformFrom hsc hprefix hnot with
    ⟨a, hstart, hR, hfail⟩
  have hcutoff : cutoff ≤ a := by
    by_contra hnotCutoff
    have hlt : a < cutoff := Nat.lt_of_not_ge hnotCutoff
    have hnextCutoff : a + 1 ≤ cutoff := Nat.succ_le_of_lt hlt
    have hnextStart : start ≤ a + 1 := le_trans hstart (Nat.le_succ a)
    exact hfail (hprefix (a + 1) hnextStart hnextCutoff)
  exact ⟨a, hcutoff, hstart, hR, hfail⟩

/-- Interval-finset scanner form of
`exists_next_failure_of_verifiedPrefix_of_not_uniformFrom`. -/
theorem exists_next_failure_of_verifiedOn_Icc_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc start cutoff) R)
    (hnot : ¬ UniformFrom start R) :
    ∃ a : ℕ, start ≤ a ∧ R a ∧ ¬ R (a + 1) :=
  exists_next_failure_of_verifiedPrefix_of_not_uniformFrom hsc
    ((verifiedOn_Icc_iff_verifiedPrefix start cutoff R).mp hverified) hnot

/-- Interval-finset scanner form of
`exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom`. -/
theorem exists_next_failure_at_or_after_cutoff_of_verifiedOn_Icc_of_not_uniformFrom
    {R : ℕ -> Prop} {start cutoff : ℕ}
    (hsc : start ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc start cutoff) R)
    (hnot : ¬ UniformFrom start R) :
    ∃ a : ℕ, cutoff ≤ a ∧ start ≤ a ∧ R a ∧ ¬ R (a + 1) :=
  exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom hsc
    ((verifiedOn_Icc_iff_verifiedPrefix start cutoff R).mp hverified) hnot

#print axioms verifiedOn_not_force_uniform
#print axioms verifiedOn_Icc_iff_verifiedPrefix
#print axioms prefixModel_verifiedPrefix
#print axioms verifiedPrefix_not_force_uniform
#print axioms two_rung_floor_evidence_not_uniform
#print axioms two_rung_floor_interval_evidence_not_uniform
#print axioms not_uniformFrom_iff_exists_failure
#print axioms not_successorStep_iff_exists_next_failure
#print axioms uniformFrom_of_base_and_successor_step
#print axioms uniformFrom_of_verifiedPrefix_and_successor_step
#print axioms uniformFrom_of_base_and_successorStep
#print axioms uniformFrom_of_verifiedPrefix_and_successorStep
#print axioms uniformFrom_of_verifiedOn_Icc_and_successorStep
#print axioms not_successorStep_of_verifiedPrefix_of_not_uniformFrom
#print axioms not_successorStep_of_verifiedOn_Icc_of_not_uniformFrom
#print axioms exists_next_failure_of_verifiedPrefix_of_not_uniformFrom
#print axioms exists_next_failure_of_verifiedOn_Icc_of_not_uniformFrom
#print axioms exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom
#print axioms exists_next_failure_at_or_after_cutoff_of_verifiedOn_Icc_of_not_uniformFrom

end ArkLib.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier
