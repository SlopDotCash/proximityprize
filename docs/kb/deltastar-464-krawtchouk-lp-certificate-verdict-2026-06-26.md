# Issue #464: Krawtchouk LP certificate verdict

Date: 2026-06-26.

Status: **route refuted as a domain-blind plain-RS floor proof**, not a delta-star proof.

## Thesis

The latest #464 sweep asked whether a Kravchuk/Krawtchouk moment-interlacing or LP certificate could
pin the plain smooth-domain RS floor while avoiding Paley/BGK.  The answer on this branch is no for
the domain-blind version of that route.

The obstruction is structural.  Reed-Solomon codes evaluated on any `n` distinct field points are
MDS, so their weight enumerator depends only on `(n, k, q)`.  The MacWilliams transform is the
Krawtchouk transform of that enumerator, and therefore the dual weight distribution is the same MDS
data for the smooth multiplicative subgroup, a random domain, and an arithmetic-progression domain.
Any certificate that only consumes this data has forgotten the evaluation domain before it reaches
the prize inequality.

Plain δ* past Johnson is domain-sensitive: the smooth subgroup is the bad case because of the
Gauss-period / Paley spectrum.  A certificate that is invariant under replacing the smooth subgroup
by any other MDS evaluation domain can at best rederive the Johnson or Parseval/second-moment
ceiling.  To become relevant past Johnson, it must inject extra smooth-domain phase or cocycle input;
that extra input is the Paley/BGK object.

## Lean Surface

New in `ArkLib/Data/CodingTheory/ProximityGap/Frontier/DelsarteLPNoGo.lean`:

```lean
domainBlind_bound_transfers
domainBlind_counterexample_refutes
```

These theorems formalize the abstract obstruction:

- if a bound is certified from an invariant `inv` alone, it transfers unchanged between any two
  domains with the same `inv`;
- if a same-invariant reference domain violates the proposed ceiling, no invariant-only certificate
  can be a valid uniform upper-bound proof.

For the Krawtchouk/MacWilliams route, `inv` is the MDS weight-enumerator data and its Krawtchouk
dual.  The theorems deliberately do not assert a numerical RS bound; they record the exact logical
place where a domain-blind LP certificate stops being capable of proving a smooth-domain-only floor.

Existing neighboring no-go anchors:

- `DelsarteLPNoGo.parseval_lp_extremal`: a degree-1 Delsarte/LP relaxation of the period house has
  optimum exactly equal to the Parseval mass, so it cannot beat the trivial ceiling.
- `ProximityGap.A5Terwilliger.terwilliger_reduces_to_wall`: the Terwilliger/Krawtchouk operator norm
  is the Gauss-period wall itself.
- `ArkLib.ProximityGap.Frontier.AvKreinCometric.krein_cometric_reduces`: the cometric/Krein dual LP
  coincides with the primal LP on the formally self-dual cyclotomic scheme.
- `ProximityGap.Frontier.FIResolventEdge.resolvent_edge_reduces`: interlacing gives the wrong
  direction and resolvent moments reduce to the same Wick-depth input.

## Probe Evidence

`scripts/probes/probe_c40_macwilliams_bch_weightdist.py` was rerun for this pass.  It confirms:

- P1: the RS MDS weight distribution is identical for the smooth subgroup, a random domain, and an
  arithmetic-progression domain with the same `(n, k, q)`;
- P2: MacWilliams maps the RS MDS weight distribution to the MDS weight distribution of the dual;
- P3: the weight-distribution / second-moment list bound becomes vacuous beyond Johnson in the
  tested `n = 16` rates;
- P4: far-line list behavior is domain-dependent and is invisible to the weight distribution.

The Levenshtein kernel probes are not validation dependencies here.  Their route note records the
separate directionality issue: Levenshtein/Delsarte packing LPs naturally give lower bounds on
coherence, while the prize needs an upper bound on the fixed smooth-domain coherence.  In this
environment those scripts require `sympy`, which was not installed during this pass.

## Verdict

The Krawtchouk/MacWilliams/Levenshtein LP idea remains useful as a no-go and Johnson-bound
rederivation, but not as a Paley-free proof of the plain smooth-domain δ* floor.  A winning version
would have to add a domain-sensitive smooth-subgroup phase input before the LP step; once it does
that, the load-bearing ingredient is again the Gauss-period/BGK sup-norm wall, not the
domain-blind Krawtchouk certificate.
