# I031 sub-Gaussian tail falsifier (#464, 2026-06-26)

The I031 route reduces the useful sup bound to a named analytic input:

```lean
SubGaussianTailBound S C m
```

This says every positive threshold `s` has empirical tail count bounded by
`m * exp(-(s^2)/(2*C))`.  The new scanner-facing theorem in
`ArkLib/Data/CodingTheory/ProximityGap/I031SubGaussianMaxBridge.lean` is:

```lean
not_SubGaussianTailBound_iff_exists_tail_count_gt
```

It turns failure of the full tail input into one concrete witness:

```text
exists s > 0,
  m * exp(-(s^2)/(2*C)) < #{v in S : s < v}
```

The period-specialized wrapper is:

```lean
not_periodSubGaussianTailBound_iff_exists_tail_count_gt
```

So the I031/BGK wall now has the same exact failure shape as the new stack
domination and representative-cover sockets: either prove the named input, or
exhibit the smallest threshold where the measured period-magnitude tail beats
the Gaussian envelope.

This does not close the delta-star floor.  It makes the I031 residual testable:
future numeric or formal attempts can search directly for a threshold/count
certificate instead of manipulating an opaque negated universal.
