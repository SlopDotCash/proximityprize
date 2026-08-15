# G210: depth-two tail-floor equality is a per-prime collision-free certificate

Date: 2026-07-11 MDT / 2026-07-12 UTC
Issue: #466 / #509
Branch: `research/proximity-prize`

## Result

G209 proves the unconditional dyadic floor

```text
sum_gamma S_gamma^2 >= n^2 (2n-3).
```

Write every occupied cross-orbit mass as `S_gamma = n k_gamma`. The CORE object supplies

```text
k_gamma >= 1,
sum_gamma k_gamma = n-1,
number of occupied classes <= n/2.
```

G210 proves the exact equality case. For even `n >= 2`,

```text
sum k_gamma^2 = 2n-3
```

if and only if the class-count cap is saturated and every `k_gamma` is `1` or `2`. The sum then forces exactly one `1` and `n/2-1` twos. Thus `[2,...,2,1]` is the unique minimizing histogram up to permutation.

## Characteristic-p interpretation

Let `G=<g>` have even order `n`, and put `m=n/2`. Ordered pair sums split by exponent difference.

- Difference `d=0` contributes one orbit, weight `1`, quotient label `L_0=2^n`.
- Each involution pair `{d,n-d}`, `1 <= d < m`, contributes two orbits, weight `2`, quotient label
  `L_d=(1+g^d)^n`.

The realized partition is obtained by merging equal labels among

```text
(L_0,1), (L_1,2), ..., (L_(m-1),2).
```

Therefore the G209 floor is attained exactly when these `m` labels are pairwise distinct. A collision is equivalent to

```text
(1+g^d)^n = (1+g^e)^n
<=> (1+g^d)/(1+g^e) = a in G
<=> 1+g^d = a(1+g^e),
```

a direct characteristic-p weighted kernel relation.

The exact probe verifies the primitive-label merge against direct ordered-pair enumeration. It also reproduces large exceptional primes:

```text
n=32, p=50177: partition [4,3,2,...,2], sumsq=73 > floor 61
n=32, p=51137: partition [4,3,2,...,2], sumsq=73 > floor 61
```

So the tempting claim “tail equals the floor for every sufficiently large prime” is not established and is wrong-shaped. The safe theorem is the per-prime equivalence above.

## FS15-FS18 and asymptotics

FS16 bounds each fixed configuration's nonzero resultant by its coefficient-mass envelope. FS17 unions finitely many fixed-depth bad sets, while FS15 shows that this almost-all-prime ladder is regime-disjoint from the logarithmic-depth prize. Applied here, those results explain why collisions are exceptional in prime families, but they do not:

1. certify either sponsor prime;
2. produce a finite eventual threshold in `p`;
3. control the simultaneous signed `r=5,6` covariance.

The collision heuristic is about `O(n^3/p)` per prime. Summed over primes it does not justify eventual absence. Density-one flatness and eventual flatness are different statements.

## Frontier consequence

The depth-two support magnitude is now exact at the structural level:

- unconditional floor: G209;
- unique equality histogram and checkable per-prime criterion: G210;
- characteristic-p failure mechanism: quotient-label collision / direct weighted relation.

This does not prove the required upper tail at the sponsor primes and does not control the signed late-Newton alignment. The remaining production object is still the simultaneous `r=5` and `r=6` cyclotomic-class covariance, the literal BGK weighted-collision wall. CORE remains open.

## Artifacts

- Lean: `Frontier/_G210TailFloorEqualityRigidity.lean`
- Probe: `scripts/probes/g210_tail_floor_flatness_certificate.py`
- Probe output: `/tmp/arklib-reports/g210_tail_floor_flatness_certificate.out`
