# DeltaStar #464: Sampled-Octave Uniformity Gate

## Artifact

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SampledOctaveUniformityGate.lean`

## Point

Issue #464 is still gated on the dyadic BGK/Paley inequality

```text
M(mu_n,p) <= C * sqrt(n * log(p/n))
```

at the worst allowed thin scale.  The measured normalized constants are favorable, with the
visible octave table bounded by about `1.49`, but a finite table is not a uniform theorem.

The new Lean gate proves this as a pure logical fact:

- `observedC100_sampleBounded`: the encoded eight-octave table is bounded by `149` in scaled
  hundredths.
- `observedC100_not_decisive`: there is a score function that agrees with that finite table
  exactly and is still sample-bounded by `149`, but violates the uniform bound from `n = 8`
  by placing a spike at `n = 2048`.
- `sampleBounded_not_force_uniform`: the same countermodel for any finite sample set missing a
  future index.
- `uniformBound_of_sampleBounded_and_coversFrom`: if the sample covers every future index, then
  the sample bound is uniform.
- `uniformBound_of_sampleBounded_and_offSampleTailBound`: the realistic consumer: finite samples
  plus a genuine off-sample tail/envelope theorem imply the desired uniform bound.
- `traceBounded_not_force_uniform`: the same obstruction for a sampled trace or subsequence that
  misses any future index.

## Consequence

This does not weaken the numerical evidence.  It prevents overclaiming from it.  The reachable
octaves are positive evidence for bounded `C`, but they cannot by themselves rule out a later
off-sample spike or a very slow `n^{o(1)}` drift.

The exact missing input is now named in reusable form:

```lean
OffSampleTailBound S start score B
```

For the real prize score this is precisely the external analytic tail/envelope theorem still
missing from the campaign.  More finite probes help calibrate the conjecture, but they do not
replace that theorem.

## Status

Negative/guardrail, axiom-clean.  No closure of the proximity gap is claimed.
