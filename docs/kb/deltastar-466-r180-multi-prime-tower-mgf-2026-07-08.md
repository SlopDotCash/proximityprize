# δ* #466 — multi-prime tower MGF invariant (2026-07-08)

## Hypothesis

R179 found that the R168 MGF is nearly invariant across a full dyadic tower at
one shared prime.  R180 tests several shared primes `p ≡ 1 mod 512`.

Probe: `scripts/probes/probe_r180_multi_prime_tower_mgf.py`.

## Result

```text
p          minMGF   maxMGF   span     maxGrid  minLow  maxS1   maxS4
--------------------------------------------------------------------------------------
262657     1.151848 1.157095 0.005247 1.200871 0.4815  0.3260  0.0456
265729     1.151848 1.156431 0.004582 1.201490 0.5111  0.3253  0.0501
270337     1.151849 1.156067 0.004219 1.200155 0.5076  0.3271  0.0446
275969     1.151849 1.154878 0.003029 1.199815 0.5113  0.3255  0.0492
278017     1.148968 1.154803 0.005835 1.198874 0.5028  0.3333  0.0493
279553     1.151849 1.156202 0.004353 1.200676 0.5055  0.3388  0.0495

summary
worst_mgf_span=0.005835 at p=278017
```

For every tested prime and every level `n ∈ {16,32,64,128,256,512}`:

```text
MGF(1/8) ≈ 1.149..1.157
grid0.5 certificate ≤ 1.2015
```

## Verdict

The tower-MGF invariant is not a one-prime accident.  It is very stable across
shared primes.

Updated proof target:

```text
Prove a dyadic tower recurrence or invariant that keeps
  (1/M) Σ exp(X_C/8)
inside a small interval near 1.16.
```

This would imply the R168 residual with enormous slack (`≤2`) and bypass the
false moment-ratio monotonicity route entirely.
