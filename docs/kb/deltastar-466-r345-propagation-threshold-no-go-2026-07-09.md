# R345: No-isolated-spike propagation has an n^(3/4) threshold

The exact quotient-walk fixed point gives

```
P f = (f^2 - n)/(n-1).
```

At a maximum `f=M`, the mean of the `H-1` neighbors is therefore
`(M^2-n)/(n-1)`.  R344 found small conditional variance at finite maximizers,
suggesting that a high state might force many high neighbors.

The production scaling refutes that shortcut under any natural `sqrt(n)`
conditional-noise estimate.  A constant signal-to-noise ratio requires

```
(M^2-n)/(n-1) >= c sqrt(n),
```

equivalently

```
M^2 >= n + c(n-1)sqrt(n),
```

so `M` must be of order `n^(3/4)`.  By contrast the prize scale is
`M^2=C n log m`, and propagation would require

```
sqrt(n) <= C log m.
```

At `n=2^30`, `m=2^128`, the two sides are approximately `32768` and `88C`.
Thus the finite probes' visible first-neighbor propagation disappears
asymptotically unless one proves a far stronger extreme-state variance bound,
roughly `Gamma(max)=O((log m)^2)` rather than `O(n)`.

Both algebraic implications are Lean-checked in
`_R345PropagationThresholdNoGo.lean`.  This closes the ordinary local-variance
propagation route at the prize scale.  A successful entropy approach would
need arithmetic variance collapse by a factor `n/(log m)^2`, which is itself a
new worst-case phase-cancellation theorem.
