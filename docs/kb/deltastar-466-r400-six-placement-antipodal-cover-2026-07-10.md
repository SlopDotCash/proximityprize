# Issue #466 R400: six-placement antipodal cover

## Result

The 24 coordinate permutations of an insertion `(x,-x,u,v)` contain two independent systematic
duplications. Swapping `u,v` is absorbed by swapping the residual pair, and, when `G` is closed under
negation, swapping `x,-x` is absorbed by replacing `x` with `-x`. Quotienting both actions leaves
exactly six cells, one for each choice of the two antipodal coordinate positions.

`_R400SixPlacementAntipodalCover.lean` proves, without a residual hypothesis,

```text
antipodalCover G c = antipodalCoverSix G c
|antipodalCover G c| <= 6 |G| |pairFiber G c|
|fourFiber G c| = |primitiveFourFiber G c| + |antipodalCover G c|
|fourFiber G c| <= |primitiveFourFiber G c| + 6 |G| |pairFiber G c|.
```

The normalization of all 24 permutations into the six representatives is kernel-checked by finite
decision over `S₄`; transport of tuple witnesses uses explicit proved identities for both swaps.
The axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Consequence for the live arithmetic target

R397/R399 refuted universal ordered pair caps `4` and `8`; the first observed value above eight is
`9` at `n=256`. R400 means that even a cap of nine contributes only `54|G|`, leaving a primitive
budget of `51|G|` under the desired `105|G|` total. More generally, primitive coefficient `A` and
pair coefficient `B` now cost exactly `A+6B` in the overlap-blind consumer.

For the hostile `n=256`, `p=67280421310721`, `c=1,2` instance, direct enumeration of the matching
pair-list products gives:

```text
fourFiber       = 24865 = 97.12890625 n
antipodalCover  = 13720 = 53.59375000 n
primitiveFiber  = 11145 = 43.53515625 n
```

Thus the observed pair multiplicity `9` contributes within `54n`, and the observed primitive part
fits the complementary `51n` budget. The Lean file packages these as the explicitly named residuals
`PairMultiplicityNine` and `PrimitiveFourBoundFiftyOne`, and proves their exact conditional consumer
`51 + 6*9 = 105`. Neither residual is asserted unconditionally.

### Preferred parity-stable split

The universal `9` formulation is awkward: an off-diagonal ordered pair fiber has even cardinality,
so `<=9` silently asks for `<=8` whenever no diagonal representation exists. The file therefore
also packages the more robust split

```text
PairMultiplicityTen
PrimitiveFourBoundFortyFive
45 + 6*10 = 105.
```

This split is numerically tighter on the primitive side but survives the hostile sample
(`43.53515625n < 45n`) and gives one extra pair support of parity headroom. It is the preferred
producer target until broader probes prove or refute either component.

Additional adversarial Fermat-factor checks did not produce monotone growth:

```text
n=512,  p=1238926361552897: pair max 4, rep4(1)/n = 29.990234375,
                              primitive(1)/n = 12.052734375
n=1024, p=7455602825647884208337395736200454918783366342657:
                              pair max 4, rep4(1)/n = 29.9951171875
```

This is a genuine improvement of the finite four-fiber reduction, not a proof of the remaining
arithmetic estimates and not yet a proof of the Proximity Prize theorem. In particular, it is a
fixed-depth result; the FS16--FS18 resultant ladder on `research/proximity-prize` confirms that the
prize residual is uniform control at logarithmic depth, not another fixed-depth envelope.
