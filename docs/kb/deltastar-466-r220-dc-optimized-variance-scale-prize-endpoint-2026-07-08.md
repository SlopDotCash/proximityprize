# δ* #466 — R220 DC-optimized variance-scale prize endpoint

R219 consumes the ratio scale condition

```text
(2 * exp 1 * |G| * k) / σ^2 ≤ 4 * log 2.
```

R220 rewrites this into the more natural variance lower-bound form:

```text
2 * exp 1 * |G| * k ≤ (4 * log 2) * σ^2.
```

The theorem

```text
prize_sq_of_dcOptimized_variance_scale
```

composes this arithmetic bridge with R219.  The conditional route is unchanged:
`DCEnergyBound G k`, `k ≥ log |F|`, the variance-scale inequality above, and
the downstream moment bridge imply the squared prize endpoint.

Status: deterministic real-arithmetic wrapper.  It makes the normalization
input easier to supply, but does not prove the DC-subtracted energy estimate or
the downstream moment bridge.
