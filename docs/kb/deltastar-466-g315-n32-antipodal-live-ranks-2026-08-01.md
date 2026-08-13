# G315: the antipodal model persists at `n=32` for live ranks

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G315 stress-tests the antipodal-pair explanation one toy order higher than the `n=16` all-rank audit.
At the certified Proth prime

```text
p = 111*2^128 + 1
```

with witness `5`, it checks `n=32` at the live ranks `r=5,6`.

The pure antipodal-pair model gives:

```text
coefficient 1: r=5 dot=0,        r=6 dot=0
coefficient 2: r=5 dot=20115200, r=6 dot=200992512
```

The exact finite-field sparse subset-histogram computation matches these model dots:

```text
coefficient 1:
  r=5 A=-7415276503040,   dot=0
  r=6 A=-186864967876608, dot=0

coefficient 2:
  r=5 A=+759778113246774813208690492278676928490593775360,  dot=20115200
  r=6 A=+7591757056558709115750550940264470531009269655296, dot=200992512
```

So the certified-scale antipodal model is not only an `n=16` all-rank artifact; it also matches the
next toy order at the live ranks.

## Scope

This is still finite evidence, not a production theorem. It checks `n=32` only at ranks `5,6`, not
the production order `n=2^30` or the production rank window. The useful content is directional:
the antipodal-pair normal form has survived the first larger-order live-rank stress test.

## Artifact

- Probe: `scripts/probes/g315_n32_antipodal_live_ranks.py`
- Output: platform temp directory `arklib-reports/g315_n32_antipodal_live_ranks.out`
