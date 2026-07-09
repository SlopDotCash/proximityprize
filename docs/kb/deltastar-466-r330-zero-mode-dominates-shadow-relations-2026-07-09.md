# #466 R330: zero mode dominates every shadow relation

## Result

`Frontier/_R321ShadowAutocorrelationDoubling.lean` identifies the mass of a realized
depth-`r` kernel relation `d` with the doubled-depth characteristic-zero histogram:

```text
shadowRelationMass(d) = NR(2m, m, 2r, d).
```

`Frontier/_R330ZeroModeDominatesShadowRelations.lean` proves the missing pointwise
positive-definiteness bound

```text
NR(2m, m, 2r, d) <= NR(2m, m, 2r, 0)
                    = shadowEnergy(2m, m, r).
```

The proof is finite and Fourier-free.  Pairs of depth-`r` shadows with fixed difference
`d` form a matching.  Apply `2ab <= a^2+b^2` to each edge; the two endpoint projections
are injective, so each squared histogram weight occurs at most once on either side.  The
zero-difference matching is exactly the diagonal.

Composing this with R314 gives the count-only collision bound

```text
shadowCollisionMass
  <= card(shadowKernelRelations) * shadowEnergy,

rEnergy(powerRootSet, r)
  <= (card(shadowKernelRelations) + 1) * shadowEnergy.
```

## Significance and delimiter

The R314 decomposition left two obligations for its uncentered collision mass: count
realized sparse kernel relations and bound the histogram autocorrelation carried by each
relation.  R330 discharges the second obligation unconditionally and with the sharp
universal zero-mode constant.

This endpoint composes directly with:

- R315: every realized relation owns a nonzero cyclotomic resultant divisible by `p`;
- R320: every realized relation has coefficient `L1` mass and support at most `2r`;
- R323: the resultant is the exact principal recurrence-lattice index.

The result does **not** reduce the corrected prize core to a small raw relation count.  The
prize target subtracts the mandatory DC mass `n^(2r)`, while the uniform zero-mode cap loses
that subtraction.  R330 proves the corresponding delimiter:

```text
n^(2r) <= q * (card(shadowKernelRelations) + 1) * shadowEnergy.
```

Thus the DC floor itself forces the count-only factor to be large.  A winning use of the
relation decomposition must retain relation-length weights, such as the R322 factorial
endpoint envelope, or prove a directly centered estimate.  The generic count of all sparse
signed vectors is far too large, and R315/R320/R323 currently supply no suitable fixed-prime
cardinality bound.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R330ZeroModeDominatesShadowRelations.lean
```

passed on 2026-07-09 with no `sorryAx` in the exported theorem audits.
