# δ* #466 — R219 DC-optimized scale prize endpoint

R219 composes R218 with the R213 normalized-square prize consumer.

The theorem

```text
prize_sq_of_dcOptimized_scale
```

keeps two orders separate:

```text
k : DC-subtracted energy order proving the child MGF residual
r : downstream R168/S11 moment-bridge order
```

The conditional route is now:

```text
DCEnergyBound G k
k ≥ log |F|
(2 * exp 1 * |G| * k) / σ^2 ≤ 4 * log 2
standard normalized-parent moment bridge
```

implies the concrete squared prize endpoint for the nonzero normalized-square
dilation parent.

Status: deterministic composition only.  The prize is not closed; the remaining
load-bearing inputs are the DC-subtracted energy estimate, the normalization
scale inequality, and the downstream moment bridge.
