# R314 c=3 Template-Family Multiplicity Law

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Summary

R314 compresses the R313 normalized-template data into the multiplicity laws that
an actual finite-combinatorial proof has to explain.  It confirms, for the
dangerous `c = 3` primes at `n = 32, 64, 128`, that the template families have
the exact occurrence totals needed to recover the R311 signature histogram.

This remains an obstruction lane, not a prize solution.  The value is that the
opaque collision table is now reduced to a small enumeration theorem plus a
single nontrivial small-family multiplicity law.

## Artifacts

- Probe: `scripts/probes/probe_r314_c3_template_family_law.py`
- Output: `scripts/probes/_out_466_r314_c3_template_family_law.txt`
- Lean socket:
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R314C3TemplateFamilyToMass.lean`

## Verified Samples

The probe checks:

- `n = 32`, `p = 21523361`, with `g^5 = -3`;
- `n = 64`, `p = 926510094425921`, with `g^21 = 3`;
- `n = 128`, `p = 1716841910146256242328924544641`, with `g^21 = 3`.

For all three samples:

- the large signature `(3n - 3, 3, 1)` has exactly two normalized templates and
  `n` total occurrences;
- the middle signature `(6, 3, 3)` has exactly twelve normalized templates and
  `2n` total occurrences;
- the small signature `(6, 3)` has exactly `6(n - 7)` normalized templates and
  `n(n - 7)` total occurrences.

Together with R312, these totals are precisely enough to recover the relation-web
mass formula `60n^2 - 90n`.  The R314 Lean socket proves this consumer step
directly and checks with `scripts/pg-iterate.sh`.

## New Proof Target

The next hard theorem should be stated at the template-family level:

```lean
C3RelationWebTemplateFamilyLaw:
  under the nondegenerate signed relation g^h = ±3,
  the positive depth-3 collision fibers decompose into
    large: 2 templates, total occurrence n;
    middle: 12 templates, total occurrence 2n;
    small: 6(n - 7) templates, total occurrence n(n - 7).
```

The large class is explained by the signed identities `±3 = ±2 ± 1` and
`g^(m-h) = -g^(-h)`.  The middle class is a twelve-template boundary family.  The
small class is the remaining real obstacle: the data strongly suggests six
one-parameter support families with seven forbidden offsets, but the occurrence
distribution is not uniform and still needs a closed counting argument.

## Why This Matters

R311 asked for a direct signature histogram.  R313 showed the histogram comes
from normalized vector templates.  R314 identifies the exact template totals
needed for the histogram, separating the proof into:

1. classify the possible template shapes;
2. count their occurrences;
3. feed the resulting signature totals into the already-proved R312 mass bridge.

That is a smaller and more structural target than brute-force classifying all
fibers modulo `p`.
