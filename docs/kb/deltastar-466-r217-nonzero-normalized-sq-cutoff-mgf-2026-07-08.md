# δ* #466 — R217 nonzero normalized-square cutoff MGF

R213 names the one-child analytic socket:

```text
MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖^2 / σ^2) 2 (1/4).
```

R217 records the elementary cutoff that implies it:

```text
∀ b ∈ nonzeroFreqs, ‖η_G(b)‖^2 / σ^2 ≤ 4 * log 2.
```

Then every exponential weight satisfies

```text
exp ((1/4) * (‖η_G(b)‖^2 / σ^2)) ≤ exp (log 2) = 2,
```

so the average quarter-MGF is at most `2`.

Status: deterministic scalar bridge only.  This does not prove the prize
concentration estimate, but it pins the exact sup-cutoff threshold that would
discharge the R213 residual.
