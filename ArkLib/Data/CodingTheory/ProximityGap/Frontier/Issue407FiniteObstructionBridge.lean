/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FiniteObstructionGoodPrime
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Issue407SaturatedIncidence

/-!
# Finite-obstruction bridge for the Issue407 bad-prime consumer

`FiniteObstructionGoodPrime` proves the arithmetic pigeonhole step: if every bad candidate prime
divides a nonzero obstruction `D`, then a candidate window with more primes than `omega(D)` contains
a prime outside the bad set.

`Issue407SaturatedIncidence` already consumes a prime outside a finite bad-prime certificate to
transfer characteristic-zero saturated-profile thresholds to deployed characteristic `p` profiles.

This file composes those two pieces.  It deliberately does not prove that the Issue407 bad-prime set
divides a small obstruction; that remains the load-bearing arithmetic input.
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.Issue407

open Finset

/-- If every finite bad-prime certificate element divides a nonzero obstruction `D`, and the
candidate prime window has more primes than `D` has prime factors, then one candidate prime lies
outside the bad-prime certificate. -/
theorem exists_prime_notMem_badPrimes_of_badPrimes_dvd_obstruction
    (P badPrimes : Finset ℕ) {D : ℕ}
    (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hBadDvd : ∀ p ∈ badPrimes, p ∣ D)
    (hcard : D.primeFactors.card < P.card) :
  ∃ p ∈ P, p ∉ badPrimes :=
  ArkLib.ProximityGap.Frontier.FiniteObstructionGoodPrime.exists_not_mem_bad_of_bad_dvd_obstruction
    P badPrimes hD hprime hBadDvd hcard

/-- Finite-obstruction form of the Issue407 no-bad-reduction selector.  Once a bad-prime
certificate is covered by a nonzero obstruction `D`, a sufficiently large candidate prime window
contains a prime for which no bad reduction occurs through the certified agreement window. -/
theorem exists_noBadReductionForPrimeThrough_of_badPrimes_dvd_obstruction
    (P badPrimes : Finset ℕ) {D : ℕ} {Bad : PrimeBadReductionProfile} {W : ℕ}
    (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hBadDvd : ∀ p ∈ badPrimes, p ∣ D)
    (hcard : D.primeFactors.card < P.card) :
    ∃ p ∈ P, p ∉ badPrimes ∧ NoBadReductionForPrimeThrough Bad p W := by
  obtain ⟨p, hpP, hpbad⟩ :=
    exists_prime_notMem_badPrimes_of_badPrimes_dvd_obstruction
      P badPrimes hD hprime hBadDvd hcard
  exact ⟨p, hpP, hpbad, hcover p hpbad⟩

/-- Finite-obstruction consumer for saturated-threshold transfer.  A characteristic-zero
saturated threshold transfers to at least one candidate prime as soon as the finite bad-prime
certificate divides a nonzero obstruction with fewer prime factors than the candidate window. -/
theorem exists_deployedThreshold_of_charZeroThreshold_badPrimes_dvd_obstruction
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} (P badPrimes : Finset ℕ) {D : ℕ} {B W wStar : ℕ}
    (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hBadDvd : ∀ p ∈ badPrimes, p ∣ D)
    (hcard : D.primeFactors.card < P.card)
    (hthr : IsSaturatedThreshold I0 B W wStar) :
    ∃ p ∈ P, p ∉ badPrimes ∧
      wStar ≤ W ∧ Ip p wStar ≤ B ∧ ∀ w, w ≤ W → wStar < w → B < Ip p w := by
  obtain ⟨p, hpP, hpbad⟩ :=
    exists_prime_notMem_badPrimes_of_badPrimes_dvd_obstruction
      P badPrimes hD hprime hBadDvd hcard
  exact ⟨p, hpP, hpbad,
    deployedThreshold_of_charZeroThreshold_prime_notMem_badPrimes
      hfaith hcover hpbad hthr⟩

/-- Finite-obstruction consumer for the inverse-profile formulation.  Outside the selected good
candidate prime, the characteristic-zero max-good agreement certificate is the deployed one. -/
theorem exists_deployedMaxGoodAgreement_of_charZeroMaxGood_badPrimes_dvd_obstruction
    {Ip : PrimeIndexedProfile} {I0 : IncidenceProfile}
    {Bad : PrimeBadReductionProfile} (P badPrimes : Finset ℕ) {D : ℕ} {B W wStar : ℕ}
    (hD : D ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime)
    (hfaith : ∀ p, FaithfulOutsideBadReduction (Ip p) I0 (Bad p) W)
    (hcover : BadPrimesCoverThrough Bad badPrimes W)
    (hBadDvd : ∀ p ∈ badPrimes, p ∣ D)
    (hcard : D.primeFactors.card < P.card)
    (hmax : IsMaxGoodAgreement I0 B W wStar) :
    ∃ p ∈ P, p ∉ badPrimes ∧ IsMaxGoodAgreement (Ip p) B W wStar := by
  obtain ⟨p, hpP, hpbad⟩ :=
    exists_prime_notMem_badPrimes_of_badPrimes_dvd_obstruction
      P badPrimes hD hprime hBadDvd hcard
  exact ⟨p, hpP, hpbad,
    deployedMaxGoodAgreement_of_charZeroMaxGood_prime_notMem_badPrimes
      hfaith hcover hpbad hmax⟩

/-! ## Axiom audit -/
#print axioms
  exists_prime_notMem_badPrimes_of_badPrimes_dvd_obstruction
#print axioms
  exists_noBadReductionForPrimeThrough_of_badPrimes_dvd_obstruction
#print axioms
  exists_deployedThreshold_of_charZeroThreshold_badPrimes_dvd_obstruction
#print axioms
  exists_deployedMaxGoodAgreement_of_charZeroMaxGood_badPrimes_dvd_obstruction

end ProximityGap.Frontier.Issue407
