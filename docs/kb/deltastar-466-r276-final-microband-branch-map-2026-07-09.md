# #466 R276: final micro-band branch map

Date: 2026-07-09

## Target

The trim-five micro-band target remains:

```text
S(0.75) <= 612 / 1485
```

where `S(theta)` is residual survival after deleting the top five quotient
values.

## Branch map

Current best split:

```text
Branch A: 512 <= M < 1536
  finite CSV certificate R269/R270
  rows=465
  worst slack=0.000066

Branch B: 1536 <= M < 2048
  finite CSV certificate R275
  rows=217
  worst slack=0.010114

Branch C: M >= 2048
  analytic target:
    S(0.75) <= 0.404
  or equivalently target lower-bulk quantile:
    q60 <= 0.759
```

Update R278: the range `2048 <= M <= 8000` is now also covered by a
finite CSV certificate, so the remaining analytic branch starts at `M >= 8001`.

## Evidence for Branch C

Through `M=8000`:

```text
worst S=0.403073 at n=512, M=2538
worst q60=0.75889031 at n=1024, M=3393
```

Stratified high-index sample `8001 <= M <= 20000`:

```text
worst sampled S=0.39630883
worst sampled q60=0.74089036
```

## Remaining proof work

The micro-band subproblem is now reduced to a large-index vertical distribution
theorem:

```text
M >= 8001 => S(0.75) <= 0.404.
```

The finite/edge branches are externally reproducible and ready for a future
Lean-native certificate pass.
