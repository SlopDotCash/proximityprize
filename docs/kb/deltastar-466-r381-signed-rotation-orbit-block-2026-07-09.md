# Issue #466 R381: signed rotation-orbit block

Date: 2026-07-09

## Result

R381 proves that rotating a realized characteristic-zero shadow difference keeps it inside the
full difference family. It then proves the exact coherent-block identity

```text
sum_{e in rotationOrbit(d)} signedEndpointSummand(e)
  = card(rotationOrbit(d)) * signedEndpointSummand(d).
```

Together with R380, each nonzero depth-`r` endpoint belongs to a coherent block of size at least
`m/(2r)`. All results are axiom-clean.

## Significance

The orbit saving now acts on the exact centered discrepancy sum rather than only on an abstract
vector family. Rotation preserves membership, doubled-walk mass, kernel sign, and endpoint `L1`.
This packages the finite-field anomaly into large equal-contribution blocks. The subsequent R382
audit proves that triangle inequality is sharp inside every such block, so orbit compression alone
does not save anything. Any useful continuation must compare distinct blocks or add arithmetic
information not preserved by rotation.
