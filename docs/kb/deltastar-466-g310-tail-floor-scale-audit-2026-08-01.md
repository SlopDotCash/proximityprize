# G310: tail-floor collision scale audit

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G210 proved the exact equality criterion for the depth-two tail floor: the floor histogram
`[2,...,2,1]` is attained iff the primitive labels

```text
2^n, (1 + g^d)^n for 1 <= d < n/2
```

are pairwise distinct. G310 is a finite exact-arithmetic scale audit of that criterion.

The probe first reproduces the recorded `n=32` exceptions:

```text
p=50177: sumsq/floor = 73/61
p=51137: sumsq/floor = 73/61
```

It then sweeps every prime `p == 1 mod 32` in `(51137, 10^6]`, checking 4,578 primes. The only
additional exceptions are:

```text
65537, 68449, 156353, 194977
```

Each exception is certified twice: by primitive-label collision and by the direct relation

```text
1 + g^d = a(1 + g^e),  a in G.
```

The same certificate is clean at a large field scale. The probe verifies by Proth theorem that

```text
p = 111*2^128 + 1
```

is prime, using witness `5`. At this prime, for both `n=32` and `n=64`, the labels are pairwise
distinct and the floor is attained:

```text
n=32: sumsq/floor = 61/61
n=64: sumsq/floor = 125/125
```

## Scope

This is not an eventual-flatness theorem and not a production result. It is a finite per-prime audit.
The additional `n=32` exceptions reinforce G210's warning that "large" does not imply collision-free.
The Proth-prime cells show that the same small/medium-prime exception species does not automatically
persist at the mission-scale field size for these toy orders. The production object at `n=2^30` and
logarithmic depth remains open.

## Artifact

- Probe: `scripts/probes/g310_tail_floor_scale_audit.py`
- Output: `/tmp/arklib-reports/g310_tail_floor_scale_audit.out` on Unix-like systems, or the platform
  temp directory's `arklib-reports/g310_tail_floor_scale_audit.out`.
