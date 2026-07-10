# Issue #466 G89/G90: exact raw-word anomaly and weighted collision decoder

Date: 2026-07-10

G89 removes the hidden histogram weights from R367.  It proves that the fiber of a genuinely
shadow-off-diagonal key pair `(v,w)` among raw ordered index words has cardinality
`NR(v) * NR(w)`, and therefore rewrites the full signed discrepancy as an unweighted sum over raw
ordered word pairs.  After transporting `gsumR` to `evalVec`, this raw-word single-embedding sum is
exactly R366's `relationAnomaly`.

The shadow-off-diagonal guard is essential.  Distinct raw words can have the same characteristic-
zero shadow through antipodal cancellation; those pairs belong to the floor, not the anomaly.

G90 repairs the semantic gap in G88.  Labels lie in a finite type `A`, with an arbitrary weight map
`w : A → B` into an additive cancellation monoid.  The endpoint sector retains equality of
weighted sums, and the primitive core type retains both disjoint label bags and equality of
weighted core sums.  Maximal common-multiset cancellation preserves the weighted equation, so the
G87 corrected representation yields an injective code and the bound

```text
|CollisionCancellationSector_s|
  ≤ |PrimitiveRelationCore_s| * (r descFactorial s)^2
      * (r-s)! * |A|^(r-s).
```

Both files pass independent `pg-iterate` checks and report only the standard quotient/extensional
axioms.  G90 is an unsigned ceiling, not yet the centered production consumer.  The next exact
step is to regroup G89's signed raw-word sum by the canonical maximal-cancellation core/padding bag
triple, retaining exact `countPerms(core+padding)` stabilizer weights and the shadow-off-diagonal
guard.  That identity will expose the #505 first-incidence quantity without spending the DC budget
once per sector.
