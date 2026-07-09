# #466 R259: coupled band tradeoff

Date: 2026-07-09

## Question

R258 refuted independent caps on `S(hi)` and the thin band. R259 tests coupled
linear envelopes

```text
S(hi) + lambda * mass([0.75,hi)) <= K(lambda)
```

with `hi = 0.79049`.

Command:

```bash
python3 scripts/probes/probe_r259_coupled_band_tradeoff.py --cache-only
```

## Result

```text
lambda  K        argK
0.00    0.398653 512,760321,1485
0.25    0.402020 512,760321,1485
0.50    0.405387 512,760321,1485
0.75    0.408754 512,760321,1485
1.00    0.412121 512,760321,1485
1.25    0.416667 512,417793,816
1.50    0.421569 512,417793,816
```

For `lambda < 1`, the inequality does not upper-bound `S(0.75)` without a
separate band cap. For `lambda = 1`, it is exactly the original micro-band cap.
For `lambda > 1`, the certificate becomes looser and switches to a different
row.

## Route update

There is no useful linear coupled shortcut. The correct theorem target is the
direct micro-band cap:

```text
S(0.75) <= 612 / 1485
```

for the trim-five residual main lane, with the high-tail cap from `0.755`
handled separately by R251.
