# δ* #466 — product budget reduces to higher-rate child MGF (2026-07-08)

## Hypothesis

R183 measured the R182 paired child product budget

```text
avg exp(left/8) exp(right/8) ≤ 2.
```

R184 tests whether this can be reduced to a simpler one-level MGF bound at a
higher rate, especially `MGF_child(1/4)`.

Probe: `scripts/probes/probe_r184_product_budget_mgf_reduction.py`.

## Result

Across six shared primes and all tower steps `16→32` through `256→512`:

```text
worst product/mgf1/4 = 0.957238
at p=278017 step=128->256
product=1.334976
mgf1/4=1.394612
```

Representative rows:

```text
p          step     product  mgf1/8  mgf1/6  mgf1/4  cauchy  prod/mgf1/4
--------------------------------------------------------------------------------------------
262657     16 ->32  1.32711  1.15185 1.21817 1.38729 1.38728 0.95662
262657     32 ->64  1.32972  1.15339 1.22186 1.40320 1.40314 0.94763
262657     128->256 1.33647  1.15597 1.22725 1.41972 1.41968 0.94136
279553     128->256 1.33496  1.15620 1.22804 1.42547 1.42544 0.93651
```

The Cauchy envelope is essentially the child `MGF(1/4)`.

## Verdict

The R182 product-budget residual can likely be replaced by a simpler child
higher-rate MGF residual:

```text
avg exp(left/8) exp(right/8)
  ≤ sqrt(avg exp(left/4) · avg exp(right/4))
  ≈ MGF_child(1/4).
```

Thus a sufficient tower-step target is:

```text
MGF_child(1/4) ≤ 2.
```

This is looser than the measured value (`≈1.39..1.43`) and much simpler than a
paired-correlation theorem.  Combined with R182, it gives a clean route:

```text
child MGF at rate 1/4 ≤ 2
  ⇒ tower product budget ≤ 2
  ⇒ parent MGF at rate 1/8 ≤ 2
  ⇒ R168/S11 prize route.
```
