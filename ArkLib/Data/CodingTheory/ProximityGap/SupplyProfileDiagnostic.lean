/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SupplySizeProfile

/-!
# Diagnostic wrappers for the sub-Johnson supply profile

This file keeps two small wrappers around `supply_size_profile_mul_le` separate from
the core profile lemma.  They are useful when testing proposed smooth-domain
sub-Johnson caps: a bound on exact-minimal agreement sets and a bound on the
strict-large agreement-set mass together imply a bound on total `t`-subset supply.
Contrapositively, any supply excess has to occur in one of those two places.
-/

set_option linter.unusedDecidableInType false


open Finset

namespace ProximityGap.PairRank

variable {α : Type} [DecidableEq α]

/-- The supply profile with a separate bound on the exact-minimal layer. -/
theorem supply_profile_diagnostic_mul_le
    (S : Finset (Finset α)) {t cap exactBound massBound : ℕ}
    (ht : 1 ≤ t)
    (hmin : ∀ A ∈ S, t ≤ A.card)
    (hcap : ∀ A ∈ S, A.card ≤ cap)
    (hexact : (S.filter (fun A => A.card = t)).card ≤ exactBound)
    (hmass : ∑ A ∈ S.filter (fun A => t < A.card), A.card ≤ massBound) :
    (∑ A ∈ S, A.card.choose t) * t
      ≤ exactBound * t + massBound * (cap - 1).choose (t - 1) := by
  refine le_trans (supply_size_profile_mul_le S ht hmin hcap hmass) ?_
  exact Nat.add_le_add_right (Nat.mul_le_mul_right t hexact)
    (massBound * (cap - 1).choose (t - 1))

/-- If total supply beats the diagnostic cap, either the exact layer or the
strict-large mass already beats its proposed budget. -/
theorem exact_layer_or_strict_mass_of_supply_profile_gt
    (S : Finset (Finset α)) {t cap exactBound massBound : ℕ}
    (ht : 1 ≤ t)
    (hmin : ∀ A ∈ S, t ≤ A.card)
    (hcap : ∀ A ∈ S, A.card ≤ cap)
    (hlarge :
      exactBound * t + massBound * (cap - 1).choose (t - 1)
        < (∑ A ∈ S, A.card.choose t) * t) :
    exactBound < (S.filter (fun A => A.card = t)).card ∨
      massBound < ∑ A ∈ S.filter (fun A => t < A.card), A.card := by
  classical
  by_cases hexact : exactBound < (S.filter (fun A => A.card = t)).card
  · exact Or.inl hexact
  · right
    by_contra hmass
    have hexact_le : (S.filter (fun A => A.card = t)).card ≤ exactBound :=
      le_of_not_gt hexact
    have hmass_le : ∑ A ∈ S.filter (fun A => t < A.card), A.card ≤ massBound :=
      le_of_not_gt hmass
    have hupper := supply_profile_diagnostic_mul_le S ht hmin hcap hexact_le hmass_le
    exact (not_lt_of_ge hupper) hlarge

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.supply_profile_diagnostic_mul_le
#print axioms ProximityGap.PairRank.exact_layer_or_strict_mass_of_supply_profile_gt
