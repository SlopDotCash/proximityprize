# δ* #466 — R204 prize tower large-index arithmetic

R202 killed the universal medium-index split: rows such as
`n = 64, M = 124, p = 7937` have `MGF(1/4) > 2`.  The prize row, however, has
top quotient index

```text
Mtop = (q - 1) / n = 2^128.
```

Descending the dyadic tower from `n` to `n / 2^d` multiplies the quotient index
by `2^d`, so every child index is

```text
M(d) = Mtop * 2^d.
```

The Lean file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R204PrizeTowerLargeIndex.lean
```

records this arithmetic and proves in particular:

```text
1024 <= DyadicTowerIndex PrizeTopIndex depth
```

for every `depth`.

This matters because R203 is intentionally a large-index-only consumer.  R204
justifies aiming the final proof at the actual prize tower instead of trying to
prove a false theorem over all medium-index dyadic rows.
