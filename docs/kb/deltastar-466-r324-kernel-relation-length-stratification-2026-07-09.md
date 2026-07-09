# Issue #466 R324: kernel-relation length stratification

Date: 2026-07-09

## Result

`_R324KernelRelationLengthStratification.lean` partitions every realized relation by

```text
s = (2r - ||d||_1) / 2.
```

R322 proves that this is an integer in `[0,r)` and supplies the exact factorial endpoint
bound at that `s`.  R324 proves the exact decomposition

```text
shadowCollisionMass
  = sum_{s<r} sum_{d in relationCancellationStratum(s)} shadowRelationMass(d)
```

and the unconditional weighted-census bound

```text
shadowCollisionMass
  <= (2r)! * sum_{s<r} card(relationCancellationStratum(s)) * m^s.
```

Both exported results are axiom-clean.

## Significance

The collision analysis no longer pays the uniform worst-case `m^(r-1)` for every relation.
Relations with large `L1` length receive the much stronger weight `m^s`, with
`s = r-||d||_1/2`.  The remaining arithmetic task is therefore a weighted sparse-relation
census rather than an unweighted count of all bounded kernel vectors.

This positive decomposition still contains the expected DC main term `n^(2r)/p`; it does
not by itself prove the DC-subtracted wall.  Prize closure requires an index-`p` lattice
count with the correct main term and Wick-scale boundary error, now against the explicit
R324 cancellation-depth weights.
