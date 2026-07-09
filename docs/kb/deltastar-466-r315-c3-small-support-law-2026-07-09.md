# R315 c=3 Small Support-Pattern Law

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Summary

R315 attacks the only unresolved count left by R314: the small `(6,3)` template
family.  Forgetting coefficient signs, the data collapses to a support-pattern
law:

- with `n = 2m`, there are `3m - 9` support patterns;
- three boundary support patterns lift to two signed templates;
- every other support pattern lifts to four signed templates.

Therefore the signed-template count is

```text
4 * ((3m - 9) - 3) + 2 * 3 = 12m - 42 = 6(n - 7).
```

This proves the arithmetic part of R314's small-template count and isolates the
next hard theorem as a support classification plus a sign-lift classification.

## Artifacts

- Probe: `scripts/probes/probe_r315_c3_small_support_law.py`
- Output: `scripts/probes/_out_466_r315_c3_small_support_law.txt`
- Lean socket:
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R315C3SmallSupportToTemplateCount.lean`

## Checked Samples

The probe checks the same dangerous c=3 primes as R314:

- `n = 32`, `m = 16`, `g^5 = -3`;
- `n = 64`, `m = 32`, `g^21 = 3`;
- `n = 128`, `m = 64`, `g^21 = 3`.

In each case:

- `support_patterns = 3m - 9`;
- `lift_distribution = 2:3 4:(3m - 12)`;
- `signed_templates = 6(n - 7)`.

The three boundary patterns have a uniform form if `h` is the signed offset for
`±3`, `k = m - h`, and `2h` is reduced modulo `m`:

```text
((0, h, 2h), (0, 2h))
((0, h, k),  (h, k))
((0, k, k+1), (0, k+1))
```

up to the orientation conventions of the signed half-basis.  These are exactly
the three support patterns with only two sign lifts.

## Next Target

The next theorem should be stated before touching the full signature theorem:

```lean
C3SmallSupportPatternLaw:
  under the nondegenerate signed relation g^h = ±3, with n = 2m,
  the small (6,3) positive collision templates have
    support_count = 3m - 9
    boundary_support_count = 3
    nonboundary_support_lifts = 4
    boundary_support_lifts = 2.
```

The R315 Lean socket proves this implies the `6(n - 7)` small-template count
needed by R314.  Combined with R314 and R312, a proof of this support law would
close the count arithmetic for the c=3 obstruction.
