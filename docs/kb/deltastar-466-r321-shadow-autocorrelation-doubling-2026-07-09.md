# Issue #466 R321: shadow autocorrelation doubling

Date: 2026-07-09

## Result

`_R321ShadowAutocorrelationDoubling.lean` proves that a pair of depth-`r` signed-basis
walks whose endpoint difference is `d` is equivalent to a single depth-`2r` walk ending
at `d`.  The equivalence negates the first tuple through the antipodal index permutation
and concatenates it with the second tuple.

For every realized nonzero kernel relation `d`, this gives the exact identity

```text
shadowRelationMass g (2*m) m r d = NR (2*m) m (r+r) d.
```

Consequently the complete finite-field wraparound surplus is

```text
shadowCollisionMass g (2*m) m r
  = sum d in shadowKernelRelations g (2*m) m r, NR (2*m) m (r+r) d.
```

## Significance

The per-relation autocorrelation is no longer an independent unknown.  The remaining
proximity gap is reduced to bounding the doubled-depth characteristic-zero histogram on
the realized nonzero sparse kernel relations.  By R320, each such relation has coefficient
`L1` norm at most `2r` and support size at most `2r`; by R315, in the power-of-two regime
it also yields a nonzero annihilator divisible by the field characteristic.

## Verification

The file passes `scripts/pg-iterate.sh` and its exported theorem axiom audits contain no
`sorryAx`.
