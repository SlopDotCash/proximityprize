/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A finite-obstruction good-prime selector

Several δ* attack surfaces reduce an arithmetic cleanup step to a fixed integer obstruction:
all bad primes for a modeled configuration divide some nonzero integer `D`.  This file records the
small selector lemma that those routes need: if a candidate window contains more primes than the
number of prime divisors of `D`, one candidate prime is automatically good.

This is intentionally only a selector.  It does not prove that a given δ* obstruction has a single
integer `D`, does not supply prime density in an arithmetic progression, and does not dominate the
universal worst-stack incidence.  It is the exact finite combinatorial step that remains after those
inputs are supplied.
-/

namespace ArkLib.ProximityGap.Frontier.FiniteObstructionGoodPrime

open Finset

/-- **Finite-obstruction selector.**  Let `P` be a finite set of candidate primes and `D ≠ 0`.
If every bad candidate prime divides `D`, then at most `D.primeFactors.card` candidates can be bad.
Consequently, if `P.card` is larger than that, some candidate prime does not divide `D`.

This is the abstract "good prime exists in the window" step for resultant/bad-prime lanes. -/
theorem exists_not_dvd_of_primeFactors_card_lt
    (P : Finset ℕ) {D : ℕ} (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcard : D.primeFactors.card < P.card) :
    ∃ p ∈ P, ¬ p ∣ D := by
  classical
  by_contra hgood
  have hnone : ∀ p ∈ P, p ∣ D := by
    intro p hp
    by_contra hpD
    exact hgood ⟨p, hp, hpD⟩
  have hsub : P ⊆ D.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hnone p hp, hD⟩
  exact (not_le_of_gt hcard) (Finset.card_le_card hsub)

/-- **Bad-set formulation.**  If every bad prime divides a nonzero obstruction `D`, and the
candidate set is larger than `D.primeFactors`, then some candidate prime is outside `Bad`.

This is often the more convenient form when a route has a named bad-prime predicate and a separate
lemma saying every bad prime divides the obstruction integer. -/
theorem exists_not_mem_bad_of_bad_dvd_obstruction
    (P Bad : Finset ℕ) {D : ℕ} (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hBadDvd : ∀ p ∈ Bad, p ∣ D)
    (hcard : D.primeFactors.card < P.card) :
    ∃ p ∈ P, p ∉ Bad := by
  classical
  obtain ⟨p, hpP, hpD⟩ := exists_not_dvd_of_primeFactors_card_lt P hD hprime hcard
  refine ⟨p, hpP, ?_⟩
  intro hpBad
  exact hpD (hBadDvd p hpBad)

/-- **Cardinality-only corollary.**  Under the same obstruction hypothesis, a bad set inside `P`
has cardinality at most the number of prime divisors of `D`. -/
theorem bad_card_le_primeFactors_card_of_bad_dvd_obstruction
    (P Bad : Finset ℕ) {D : ℕ} (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hBadSub : Bad ⊆ P)
    (hBadDvd : ∀ p ∈ Bad, p ∣ D) :
    Bad.card ≤ D.primeFactors.card := by
  classical
  have hsub : Bad ⊆ D.primeFactors := by
    intro p hpBad
    exact Nat.mem_primeFactors.mpr
      ⟨hprime p (hBadSub hpBad), hBadDvd p hpBad, hD⟩
  exact Finset.card_le_card hsub

open Classical in
/-- **Local-obstruction union bound.**  If every bad candidate prime divides at least one local
obstruction integer `D i`, then the number of bad candidates is bounded by the sum of the local
prime-factor counts.

This is the finite arithmetic tax paid by universalizing a binder/configuration-local
bad-prime argument: unless the local obstructions compress to a single small `D`, the good-prime
selector compares the prime window with `∑ i, omega(D i)`, not with one obstruction count. -/
theorem bad_filter_card_le_sum_primeFactors_card_of_local_obstructions
    {ι : Type} (I : Finset ι) (P : Finset ℕ) (Bad : ℕ → Prop)
    (D : ι → ℕ)
    (hD : ∀ i ∈ I, D i ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hBadDvd : ∀ p ∈ P, Bad p → ∃ i ∈ I, p ∣ D i) :
    (P.filter Bad).card ≤ ∑ i ∈ I, (D i).primeFactors.card := by
  classical
  have hsub : P.filter Bad ⊆ I.biUnion (fun i => (D i).primeFactors) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hpP, hpBad⟩
    rcases hBadDvd p hpP hpBad with ⟨i, hiI, hpD⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, hiI, Nat.mem_primeFactors.mpr ⟨hprime p hpP, hpD, hD i hiI⟩⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

open Classical in
/-- **Good-prime selector with local obstructions.**  If the candidate prime window is larger than
the sum of the local obstruction prime-factor counts, and every bad candidate prime divides one
local obstruction, then some candidate prime is good.

This is the useful contrapositive for the universal finite-obstruction route: a proof that only
produces one obstruction per profile/configuration must still beat this summed count. -/
theorem exists_not_bad_of_local_obstructions_sum_lt
    {ι : Type} (I : Finset ι) (P : Finset ℕ) (Bad : ℕ → Prop)
    (D : ι → ℕ)
    (hD : ∀ i ∈ I, D i ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hBadDvd : ∀ p ∈ P, Bad p → ∃ i ∈ I, p ∣ D i)
    (hcard : (∑ i ∈ I, (D i).primeFactors.card) < P.card) :
    ∃ p ∈ P, ¬ Bad p := by
  classical
  by_contra hnone
  push Not at hnone
  have hfilter : P.filter Bad = P := by
    ext p
    constructor
    · exact fun hp => (Finset.mem_filter.mp hp).1
    · intro hp
      exact Finset.mem_filter.mpr ⟨hp, hnone p hp⟩
  have hle := bad_filter_card_le_sum_primeFactors_card_of_local_obstructions
    I P Bad D hD hprime hBadDvd
  rw [hfilter] at hle
  exact (not_lt_of_ge hle) hcard

-- Axiom audit (expected: no axioms beyond Lean/Mathlib proof irrelevance machinery).
#print axioms exists_not_dvd_of_primeFactors_card_lt
#print axioms exists_not_mem_bad_of_bad_dvd_obstruction
#print axioms bad_card_le_primeFactors_card_of_bad_dvd_obstruction
#print axioms bad_filter_card_le_sum_primeFactors_card_of_local_obstructions
#print axioms exists_not_bad_of_local_obstructions_sum_lt

end ArkLib.ProximityGap.Frontier.FiniteObstructionGoodPrime
