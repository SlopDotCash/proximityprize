# #466 R267: finite micro-band branch

Date: 2026-07-09

## Question

R266 splits the direct micro-band cap at `M0 = 1536`. R267 enumerates the
finite branch `512 <= M < 1536` for `n in {256,512,1024}`.

Command:

```bash
python3 scripts/probes/probe_r267_finite_microband_branch.py --cache-only
```

## Result

```text
cases=465
near_rows(slack <= 0.02)=26
```

Top rows:

```text
micro    slack    count  S        n     p          M
0.601134 0.000066 612    0.412121 512   760321     1485
0.601039 0.000161 499    0.412056 512   620033     1211
0.600614 0.000586 336    0.411765 512   417793     816
0.594872 0.006328 323    0.407828 256   202753     792
0.594258 0.006942 209    0.407407 512   262657     513
0.593423 0.007777 500    0.406835 512   629249     1229
0.591606 0.009594 537    0.405589 1024  1355777    1324
```

By level:

```text
n=256  cases=161 near=10 best=0.59487197 slack=0.00632803 p=202753  M=792
n=512  cases=151 near=8  best=0.60113378 slack=0.00006622 p=760321  M=1485
n=1024 cases=153 near=8  best=0.59160586 slack=0.00959414 p=1355777 M=1324
```

## Route update

The finite branch is small enough for a direct certificate table:

```text
512 <= M < 1536, n in {256,512,1024}: 465 rows total.
```

Only 26 rows are within `0.02` of the target. The truly knife-edge rows are the
three `n=512` rows:

```text
(p,M) = (760321,1485), (620033,1211), (417793,816).
```

This makes the R266 architecture credible:

1. direct finite certificate for `M < 1536`;
2. analytic/asymptotic large-index cap for `M >= 1536`.
