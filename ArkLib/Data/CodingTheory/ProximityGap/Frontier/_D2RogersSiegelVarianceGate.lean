/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# D2 Rogers/Siegel variance gate: random-lattice moments need a prime coupling

Issue #464 flagged arXiv:2606.27020 as a possible "Rogers/Siegel second moment" input for the
good-prime sliver.  The paper's ambient variable is a Siegel-transform statistic on a random
unimodular lattice.  The prize sliver is a different statistic indexed by primes, e.g. the
wraparound surplus or the Gauss-period house at `p ≡ 1 mod n`.

The exact missing bridge is therefore not another variance inequality; it is a coupling/pullback
from prize primes to the random-lattice probability space.  Without a map `p ↦ ω_p` and a
pointwise comparison between the prime statistic and the lattice statistic, a uniform lattice bound
does not imply any prime bound.  Conversely, once such a coupling is supplied, the transfer is
immediate.

This file records that gate axiom-cleanly.  The existing prime-indexed variance route is already
handled by `_AvBV2_VarianceOverPrimesCertificationDeficit.lean`; this file only closes the
Rogers/Siegel transplant ambiguity.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.D2RogersSiegelVarianceGate

/-- A uniform bound on an auxiliary sample statistic transfers to every prize prime only through a
pointwise coupling `pull : P → Ω` and comparison `primeStat p ≤ sampleStat (pull p)`. -/
theorem uniform_prime_bound_of_pointwise_coupling
    {P Ω : Type*} (primeStat : P → ℝ) (sampleStat : Ω → ℝ) (pull : P → Ω) (B : ℝ)
    (hcompare : ∀ p, primeStat p ≤ sampleStat (pull p))
    (hsample : ∀ ω, sampleStat ω ≤ B) :
    ∀ p, primeStat p ≤ B := by
  intro p
  exact le_trans (hcompare p) (hsample (pull p))

/-- A lower-tail exclusion also transfers only through the corresponding pointwise coupling.  If the
sample statistic is always above `T` after pulling primes into the sample space, then the prime
statistic has no value at or below `T`. -/
theorem no_good_prime_of_pointwise_lower_coupling
    {P Ω : Type*} (primeStat : P → ℝ) (sampleStat : Ω → ℝ) (pull : P → Ω) (T : ℝ)
    (hcompare : ∀ p, sampleStat (pull p) ≤ primeStat p)
    (hsample : ∀ p, T < sampleStat (pull p)) :
    ¬ ∃ p, primeStat p ≤ T := by
  rintro ⟨p, hp⟩
  have hT : T < primeStat p := lt_of_lt_of_le (hsample p) (hcompare p)
  exact not_lt_of_ge hp hT

/-- **No-coupling countermodel.**  A bounded auxiliary sample statistic is compatible with an
arbitrarily bad prime statistic.  Hence a Rogers/Siegel random-lattice moment bound, by itself,
cannot decide the prime-indexed good-prime sliver; a coupling/comparison hypothesis is
load-bearing. -/
theorem uncoupled_sample_bound_does_not_bound_primes
    {P Ω : Type*} [Nonempty P] (B : ℝ) :
    ∃ (sampleStat : Ω → ℝ) (primeStat : P → ℝ),
      (∀ ω, sampleStat ω ≤ B) ∧ (∃ p, B < primeStat p) := by
  refine ⟨fun _ => B - 1, fun _ => B + 1, ?_, ?_⟩
  · intro _; linarith
  · obtain ⟨p⟩ := ‹Nonempty P›
    exact ⟨p, by linarith⟩

/-! ## Axiom audit. -/
#print axioms uniform_prime_bound_of_pointwise_coupling
#print axioms no_good_prime_of_pointwise_lower_coupling
#print axioms uncoupled_sample_bound_does_not_bound_primes

end ArkLib.ProximityGap.Frontier.D2RogersSiegelVarianceGate
