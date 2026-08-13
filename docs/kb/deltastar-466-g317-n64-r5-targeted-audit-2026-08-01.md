# G317: targeted `n=64`, rank-5 field audit

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G316 predicts the antipodal-model dots for `n=64`:

```text
coefficient 1, r=5: dot=0
coefficient 2, r=5: dot=864230400
```

G317 checks the actual finite-field count at the certified Proth prime

```text
p = 111*2^128 + 1
```

with witness `5`. A full weighted-kernel materialization is unnecessary. Since the adjacent-rank row
`R(t)` is invariant under dilation by the subgroup `G`, the dot product can be evaluated by the
quotient identity

```text
sum_t W_a(t) R(t) = n * sum_{u in G} R(a-u),
```

where `u=z/y`. This queries `64` quotient shifts instead of expanding all `4096` ordered kernel pairs.

For `n=64,r=5`, the exact sparse subset histograms have support sizes:

```text
r=0: 1
r=1: 64
r=2: 1985
r=3: 39744
r=4: 577345
r=5: 6483776
```

The finite-field dots match the antipodal model exactly:

```text
coefficient 1: A=-19842793211953152, dot=0
coefficient 2: A=+32643142634550265248631476078696581721630936603648, dot=864230400
```

## Scope

This is a finite toy-order audit, not the production theorem. It checks `n=64` only at rank `5`.
The rank-6 histogram is expected to have about `58,573,633` support states in this sparse model, so
that case should use a lower-level or disk-backed counter rather than a normal Python dictionary.

## Artifact

- Probe: `scripts/probes/g317_n64_r5_targeted_audit.py`
- Output: platform temp directory `arklib-reports/g317_n64_r5_targeted_audit.out`
