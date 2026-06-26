# Issue #464: Rogers/Siegel variance gate

Date: 2026-06-26.

Status: **route gated by a missing prime-to-lattice coupling**, not a delta-star proof.

External source: arXiv:2606.27020, "Cusp Excursions, Lattice Points on Manifolds, and the
Mizohata-Takeuchi Conjecture" <https://arxiv.org/abs/2606.27020>.

## Thesis

The latest #464 sweep listed arXiv:2606.27020 as a possible D2 lever: use Rogers/Siegel-transform
second moments to decide the surviving good-prime lower-tail sliver.  The paper is real
random-lattice machinery: it studies cusp excursions and lattice points near manifolds by averaging
over unimodular lattices.  That is not the same probability space as the prize variable

```text
W_r(p), M(p), or E_r(p) indexed by primes p ≡ 1 mod n.
```

The required missing object is a coupling:

```text
p ↦ Λ_p
prime statistic at p  <=/≈  Siegel statistic at Λ_p
```

or a distributional identity proving that the random-lattice second moment is the prime-window
second moment of the wraparound surplus.  Without this, a variance theorem over random lattices has
no logical force on the adversarial prize prime.

## Lean Surface

New in `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D2RogersSiegelVarianceGate.lean`:

```lean
uniform_prime_bound_of_pointwise_coupling
no_good_prime_of_pointwise_lower_coupling
uncoupled_sample_bound_does_not_bound_primes
```

These theorems record the exact gate:

- a uniform bound on an auxiliary sample statistic transfers to all primes only through a pointwise
  pullback/coupling from primes into the sample space;
- a lower-tail exclusion transfers only through the corresponding lower comparison;
- without such a coupling, a bounded sample statistic is compatible with an arbitrarily bad
  prime-indexed statistic.

The last theorem is the honest no-coupling countermodel.  It prevents the move "Rogers/Siegel
variance is small, therefore the prize prime is controlled" unless the missing comparison is
supplied as a real theorem.

## Relation To Existing Prime-Variance Work

This does not replace the existing prime-indexed variance no-go:

```lean
ArkLib.ProximityGap.Frontier.AvBV2.chebExc_card_le
ArkLib.ProximityGap.Frontier.AvBV2.certification_deficit_exceeds_paley
ArkLib.ProximityGap.Frontier.AvBV2.structural_set_cannot_isolate_extremum
```

in `Frontier/_AvBV2_VarianceOverPrimesCertificationDeficit.lean`.

That file assumes the variance is already over the actual prime set and still shows the
certification deficit: to certify every prime in a window from Chebyshev, the threshold rises from
`μ` to `μ + √|P| σ`.  At prize scale `|P| ≍ n^3/log n`, this is an `n^{3/2}` loss unless the
relative standard deviation is far smaller than the measured prime-window behavior.  It also records
that structural avoidability, such as removing a simple `v₂(p-1)` exceptional set, does not
isolate the worst prime.

The new Rogers/Siegel gate is one layer earlier: arXiv:2606.27020 is not even prime-indexed until a
coupling identifies its random-lattice statistic with the prize's wraparound statistic.

## Verdict

Rogers/Siegel second-moment technology is a plausible language for modeling lower tails, but it is
not yet a route to the plain-RS floor.  To become relevant it must first produce a prime-to-lattice
coupling or distributional identity for `W_r(p)`/`M(p)`.  If such a coupling is found, the problem
then falls back to the existing `_AvBV2` certification-deficit gate.  Without it, the D2 transplant
is a probability-space mismatch, not a proof of the Paley/BGK floor.
