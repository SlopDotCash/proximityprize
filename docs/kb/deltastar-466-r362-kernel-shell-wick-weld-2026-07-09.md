# Issue #466 R362: kernel-shell Wick weld

Date: 2026-07-09

## Result

R362 defines the full evaluation-kernel shell

```text
K_L(g) = {d in Z^m : ||d||_1 = L and eval_g(d) = 0}.
```

Every realized relation in cancellation stratum `s` is proved to lie in `K_{2(r-s)}(g)`.
Thus the square-root shell census

```text
k! * #K_{2k}(g) <= 3^k * m^k       for k <= r
```

implies R355's `GeneratorWebCensus` and therefore

```text
r! * shadowCollisionMass <= 4^r * (2r)! * m^r.
```

The complete implication is axiom-clean.

## Significance

This is the exact theorem-level interpretation of R361's finite observation that the bad
`n=64` endpoint has 40 vectors in its first nonzero `L1` shell. Collision multiplicity is
handled by R322's endpoint envelope in the shallow regime.

The raw shell target demands a square-root saving over the ambient `m^(2k)` signed shell. It is
plausible only before the DC crossover `k ≈ log_m |F|`. At deep prize moments the kernel's
uniform population is approximately the ambient shell divided by `|F|`, so `KernelShellCensus`
is not the correct global conjecture. The remaining deep-wall target is a centered weighted-shell
discrepancy after subtracting that uniform term, matching `DCEnergyBound` exactly.
