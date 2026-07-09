# δ* #466 — vectorized large-anchor tail stress (2026-07-08)

## Hypothesis

R198's scalar exact engine was too slow for the largest multi-million-coset
rows.  R199 keeps the exact same Gauss-period computation but evaluates coset
representatives in NumPy chunks:

```text
η_b = Σ_{h∈H} exp(2πi b h / p).
```

## Probe

File: `scripts/probes/probe_r199_vectorized_large_anchor_tail.py`.

Smoke test:

```text
python3 scripts/probes/probe_r199_vectorized_large_anchor_tail.py --only-small --chunk 8192
```

Huge-anchor run:

```text
python3 scripts/probes/probe_r199_vectorized_large_anchor_tail.py --chunk 32768
```

## Result

Huge-anchor exact run:

```text
tested = 4
max_positive_excess = 0
```

Rows:

```text
excess    mgf1/4  maxX    M        n     p
-2.725    1.4103  27.172  2097179  128   268438913
-3.944    1.4113  19.085  65541    256   16778497
-9.002    1.4101  17.291  65548    256   16780289
-9.927    1.4101  23.688  2097171  128   268437889
```

## Verdict

The previously interrupted R198 large-anchor rows now run exactly in seconds
and still satisfy the R189 large-index tail law

```text
N(T) <= (3/5) M exp(-T/2) + 2.
```

This removes the immediate computational bottleneck for the large-index stress
campaign and strengthens the evidence for the R197 large branch.
