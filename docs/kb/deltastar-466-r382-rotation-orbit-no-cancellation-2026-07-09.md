# Issue #466 R382: rotation-orbit no-cancellation audit

Date: 2026-07-09

## Result

R381's coherent rotation blocks do not themselves yield an upper-bound saving. R382 proves the
exact identity

```text
abs(sum_{e in orbit(d)} signedEndpointSummand(e))
  = sum_{e in orbit(d)} abs(signedEndpointSummand(e)).
```

Thus triangle inequality is sharp on every orbit. The lower bound
`m <= card(orbit(d)) * 2r` from R380 is paid back exactly by the repeated equal summands.

## Consequence

Pure orbit compression is cosmetic. A closing argument must obtain cancellation between distinct
orbits, or use arithmetic information beyond rotation invariance, endpoint support, endpoint L1
mass, doubled-walk multiplicity, and kernel membership. This agrees with the earlier SST orbit
compression audit while applying directly to the exact centered discrepancy derived in R365-R369.
