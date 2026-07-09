# R316 c=3 Small Support Families

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Summary

R316 upgrades the R315 support count into an explicit parametric
classification.  For the small `(6,3)` c=3 templates, every support pattern in
the tested dangerous primes belongs to exactly one of three one-parameter
families.

Write `n = 2m`, let `h` be the signed half-basis offset with `g^h = ±3`, and set
`k = m - h`.  The support patterns are:

```text
H(t) = ((0,t,h),       (0,t))       with t notin {h,k}
K(t) = ((0,t,k),       (t,k))       with t notin {k,h+1}
D(t) = ((0,t,t+h mod m),(0,t))     with t notin {h,k}
```

Each family has `m - 3` parameters, so the total support count is `3m - 9`.
This is precisely the support count consumed by R315.

## Artifacts

- Probe: `scripts/probes/probe_r316_c3_small_support_families.py`
- Output: `scripts/probes/_out_466_r316_c3_small_support_families.txt`
- Lean socket:
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R316C3SmallFamiliesToSupportCount.lean`

## Checked Samples

The probe checks the same three dangerous c=3 primes:

- `n = 32`, `m = 16`, `g^5 = -3`;
- `n = 64`, `m = 32`, `g^21 = 3`;
- `n = 128`, `m = 64`, `g^21 = 3`.

For all three:

- unknown support patterns: `0`;
- duplicates inside each family: `0`;
- `H`, `K`, and `D` each have `m - 3` parameters;
- the missing parameters match the formulas above.

## Proof Route

The c=3 small-family proof target is now split into three crisp pieces:

1. show every small positive collision support has one of the `H/K/D` forms;
2. show the excluded parameters are exactly `{h,k}`, `{k,h+1}`, `{h,k}`;
3. show the three families are disjoint except for the already-accounted boundary
   lift behavior from R315.

R316's Lean socket proves the resulting count arithmetic:

```text
3 * (m - 3) = 3m - 9
```

and the R315 socket then turns this into the small-template count `6(n - 7)`.
This gives a much more concrete route to the full `C3RelationWebTemplateFamilyLaw`.
