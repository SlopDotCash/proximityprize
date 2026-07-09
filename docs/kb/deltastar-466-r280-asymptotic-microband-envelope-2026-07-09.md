# #466 R280: asymptotic micro-band envelope

Date: 2026-07-09

## Question

After R278, the remaining micro-band branch is:

```text
M >= 8001 => S(0.75) <= 0.404
```

R280 tests whether the large-index tail appears to obey a stronger, simple
finite-size envelope.

## Probe

Script:

```text
scripts/probes/probe_r280_asymptotic_microband_envelope.py
```

Cache-only sampled command:

```text
python3 scripts/probes/probe_r280_asymptotic_microband_envelope.py \
  --min-index 8001 \
  --max-index 100000 \
  --stride 113 \
  --limit-per-n 120 \
  --top 12 \
  --cache-only
```

Output summary:

```text
cases=280 skipped=7
max S(0.75)=0.39350934 at n=1024 p=9812993 M=9583
max q60=0.72788199 at the same case
```

Dyadic buckets:

```text
[2^13,2^14): maxS=0.393509 maxq60=0.727882
[2^14,2^15): maxS=0.391680 maxq60=0.725278
[2^15,2^16): maxS=0.390197 maxq60=0.722481
[2^16,2^17): maxS=0.388867 maxq60=0.715888
```

## Candidate theorem

The data supports the much stronger asymptotic target:

```text
M >= 8192 => S(0.75) <= 0.394
```

or, in q60 form:

```text
M >= 8192 => q60 <= 0.728
```

Either theorem is far stronger than the branch requirement:

```text
S(0.75) <= 0.404
q60 <= 0.759
```

## Fit shape

For `S(0.75)` in the sampled cache:

```text
S(0.75) <= 0.390 + 0.344 / sqrt(M)
```

fits all sampled rows, with the worst row again at `M=9583`.

For q60:

```text
q60 <= 0.720 + 0.816 / sqrt(M)
```

fits all sampled rows, with the worst row at `M=13651`.

## Interpretation

The remaining branch is probably not a delicate edge case.  The empirical
frontier falls quickly once the finite certificate covers through `M=8000`.

Proof-wise, the best next target is not the original loose cap `0.404`, but a
stronger large-index regularity statement:

```text
M >= 8192 => S(0.75) <= 0.394.
```

That statement has enough slack to absorb a coarse analytic estimate, provided
the estimate sees some cancellation beyond the current Markov/second-moment
budget.

Update R281: the bridge window `8001 <= M < 8192` now has its own finite CSV
certificate, so the final analytic micro-band branch really can start at the
dyadic threshold `M >= 8192`.

Update R282: exact enumeration of `8192 <= M <= 10000` refutes the proposed
`M >= 8192 => S(0.75) <= 0.394` theorem.  The counterexample is:

```text
n=1024 p=9376769 M=9157
S(0.75)=0.39630883
```

That near-dyadic shoulder is now covered by a finite CSV certificate.  The
remaining candidate should be weakened and shifted to:

```text
M >= 10001 => S(0.75) <= 0.397
```

or simply keep the original required asymptotic branch:

```text
M >= 10001 => S(0.75) <= 0.404.
```
