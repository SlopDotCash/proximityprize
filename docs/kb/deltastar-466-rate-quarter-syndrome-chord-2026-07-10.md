# Rate-quarter syndrome-chord reduction (2026-07-10)

## Scope

This note records the live `n = 16`, `k = 4`, threshold-nine reduction inside
the unique-eight-core branch. It does not close the Proximity Prize or the
separate no-eight intermediate-core residual.

## Punctured syndrome model

Fix the unique source core `D` of size eight and puncture to its complement
`V`. The punctured code is `RS[V,4]`. For every regular outsider `gamma`, the
affine quotient point

```text
[u0 - sourceIntercept] + gamma [u1 - sourceSlope]
```

has a representative supported on the exact two-coordinate missed edge of
`gamma`. The quotient coordinate columns are four-wise independent because
`RS[8,4]` has minimum distance five.

The concrete bridge is
`regular_weightTwoSyndromeRepresentation` in
`_HalfPredecessorRateQuarterKFourUniqueCoreSyndrome.lean`.

## Strict chord bound

Let `P` be the quotient row plane. If `P` contains no coordinate column, the
graph of coordinate chords meeting `P` has degree at most two. Chord incidence
is transitive up to the forbidden diagonal: in the quotient by `P`, adjacent
columns have the same projective direction.

The handshake bound gives at most eight edges. Equality would make every
degree equal to two, while transitivity would partition the eight vertices
into closed three-vertex blocks. This is impossible. Hence the exact ceiling
is seven:

```text
chordGraph_edgeFinset_card_le_seven
weightTwoSyndromeLine_card_le_seven
```

The seven-vertex deletion companion gives at most six edges:

```text
chordGraph_edgeFinset_card_le_six
```

Since independent quotient rows make the affine quotient points
projectively injective, eight regular outsiders cannot occur in the
column-avoiding branch. The proved unique-core reduction is therefore:

```text
uniqueEightCoreResidual_quotient_degenerate
```

It leaves exactly two alternatives:

1. the two punctured received-row classes are dependent; or
2. their quotient row plane contains a coordinate column.

## Closing the two degeneracies

Both alternatives reduce to compact missed-edge families.

- A column-avoiding one-dimensional syndrome subspace meets only one chord
  support (`pair_eq_of_chordMeets_of_finrank_le_one`). Thus dependent rows
  force a common missed edge unless the one-dimensional subspace is itself a
  coordinate column.
- If that subspace is a coordinate column, every missed edge contains the
  same coordinate. Any three such edges have union of size at most four.
- With exactly one coordinate column in an independent row plane, incident
  chords contribute at most one projective point and deletion leaves at most
  six other chords. This contradicts the eight-outside lower bound
  (`uniqueEightCoreResidual_not_exactly_one_contained_column`).
- With two coordinate columns in the row plane, the two MDS columns span it.
  The nonzero coefficients in the exact error representation and four-wise
  independence force every regular missed edge to be that same contained
  pair (`regularMissedEdge_eq_of_two_contained_columns`).

For either a common edge or a fixed star, any three relevant missed edges
have union of size at most four. Their regular decoded polynomials therefore
share at least four fresh agreement coordinates. The degree-three triple
root cap puts every third point on the secant through two fixed points.
At length sixteen and threshold nine, five points on one relevant line force
its core to have size at least eight. Unique-core rigidity would then identify
that line with the source line, contradicting that the regular points are
outsiders.

The dependent branch is eliminated by
`uniqueEightCoreResidual_quotientRowsIndependent`; the two-column branch is
eliminated by `uniqueEightCoreResidual_false_of_two_contained_columns`. The
terminal synthesis is:

```text
uniqueEightCoreResidual_false
card_le_sixteen_or_no_eight_intermediate
```

Thus the global `n=16,k=4` classification is now either `|G| <= 16` or
`NoEightCoreIntermediateResidual`. There is no surviving unique-eight-core
case.

## Remaining no-eight frontier

For a no-eight residual, puncturing the source line gives the following
honest sparse-syndrome dichotomy:

```text
noEight_sparse_syndrome_dichotomy
```

- source core seven: at least thirteen source outsiders and every affine
  quotient point in punctured `RS[9,4]` has coset weight at most three;
- source core six: at least fourteen source outsiders and every affine
  quotient point in punctured `RS[10,4]` has coset weight at most four.

The remaining quantitative target is an RS-specific affine quotient-line
bound of at most twelve in the first branch or at most thirteen in the
second. Bare signature counting cannot prove it (the 24-signature affine
plane model is a counterexample), and bare MDS weight-three syndrome-line
bounds are also false. The proof must retain the coupling to the source-core
residual or its locator polynomials.

## Probe warning

`scripts/probes/probe_rate_quarter_unique_core_syndrome_signatures.py`
constructs an eight-signature cardinal model (including a five-cycle plus a
triangle at overlap size two). It is not a Reed--Solomon realization. The
transitive chord relation rules out the five-cycle, which is precisely why the
linear-algebraic quotient argument is stronger than the signature census.
