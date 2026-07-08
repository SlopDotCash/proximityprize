# δ* #466 — tower product-budget measurement (2026-07-08)

## Hypothesis

R182 reduced the tower-step MGF certificate to the paired child product budget:

```text
avg_i exp(left_i/8) exp(right_i/8) ≤ 2.
```

R183 measures this exact input across several shared dyadic tower primes.

Probe: `scripts/probes/probe_r183_tower_product_budget.py`.

## Result

Across six primes `p ≡ 1 mod 512` and all steps
`16→32, 32→64, 64→128, 128→256, 256→512`:

```text
worst_product_budget=1.336466 at p=262657 step=128->256
target <= 2.0
```

Representative rows:

```text
p          step     parentMGF productBudget maxTerm sigmaRatio
------------------------------------------------------------------------------
262657     16 ->32  1.153393  1.327107      8.229   1.99988
262657     32 ->64  1.153592  1.329719      8.050   1.99976
262657     64 ->128 1.155966  1.329924      6.922   1.99951
262657     128->256 1.154754  1.336466      7.247   1.99902
262657     256->512 1.157095  1.334972      7.989   1.99805
```

## Verdict

The R182 product-budget input is empirically stable and comfortably below the
required threshold:

```text
product budget ≈ 1.33 < 2.
```

This is the best current proof target for the tower route:

```text
For paired child periods in the dyadic split, prove
  avg exp(left/8) exp(right/8) ≤ 2.
```

Together with `σ²_parent = 2σ²_child` and
`|a+b|² ≤ 2(|a|²+|b|²)`, the R182 Lean consumer then gives the R168 MGF
residual for the parent level.
