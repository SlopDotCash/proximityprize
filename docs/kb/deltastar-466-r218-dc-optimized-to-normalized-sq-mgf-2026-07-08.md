# δ* #466 — R218 DC-optimized bound to normalized-square MGF

R217 reduced the R213 one-child MGF residual to the cutoff

```text
‖η_G(b)‖^2 / σ^2 ≤ 4 * log 2
```

over nonzero frequencies.

R218 connects that cutoff to the existing `DCOptimized` pointwise theorem.  If
`DCEnergyBound G r` holds at an order `r ≥ log |F|`, then for nonzero `b`:

```text
‖η_G(b)‖^2 ≤ 2 * exp 1 * |G| * r.
```

Therefore the R213 residual follows whenever the normalization scale satisfies

```text
(2 * exp 1 * |G| * r) / σ^2 ≤ 4 * log 2.
```

Status: deterministic bridge.  The live math is now explicit in two inputs:
the DC-subtracted energy estimate and a normalization scale large enough for
the displayed inequality.
