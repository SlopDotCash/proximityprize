/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

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
  omega

/-- The concrete `a = 4, 5` floor evidence, by itself, does not force uniformity for all `a >= 4`.
-/
theorem two_rung_floor_evidence_not_uniform :
    ¬ (∀ R : ℕ -> Prop, VerifiedPrefix 4 5 R -> UniformFrom 4 R) :=
  verifiedPrefix_not_force_uniform (start := 4) (cutoff := 5) (by norm_num)

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

#print axioms verifiedOn_not_force_uniform
#print axioms prefixModel_verifiedPrefix
#print axioms verifiedPrefix_not_force_uniform
#print axioms two_rung_floor_evidence_not_uniform
#print axioms uniformFrom_of_base_and_successor_step
#print axioms uniformFrom_of_verifiedPrefix_and_successor_step

end ArkLib.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier
