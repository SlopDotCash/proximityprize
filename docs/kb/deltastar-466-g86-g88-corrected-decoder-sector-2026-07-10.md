# Issue #466 G86–G88: corrected decoder sector bound

Date: 2026-07-10

The factorial-corrected maximal-cancellation decoder is now a proved finite encoding rather than
an assumed surjection.

- G86 uses occurrence-index bijections to select core-slot embeddings from G83M's residual
  multisets, correctly handling repeated values.
- G87 turns the equal complementary padding bags into one relative position permutation and
  reconstructs both endpoints exactly.
- G88 packages ordered disjoint residual core words as `PrimitiveCorePair`, defines the
  depth-`s` `CancellationSector`, chooses a corrected-code representation, and proves that choice
  injective because raw decoding recovers the original endpoint pair.

The resulting theorem is

```text
|CancellationSector(A,r,s)|
  <= |PrimitiveCorePair(A,s)|
     * (r descFactorial s)^2
     * (r-s)!
     * |A|^(r-s).
```

The declarations compile with `propext`, `Classical.choice`, and `Quot.sound` only.

This closes the finite decoder interface. It does not bound `PrimitiveCorePair` at growing depth,
prove the energy/Wick saddle condition for all production sectors, or produce the non-Fourier
arc-uniformity certificate needed to bound `M`. The production delta-star conjecture remains open.
