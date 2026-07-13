# δ* / #466 G268: antipodal floor wraparound gap

## Verdict

The eventual-positive `n=8` thin tail in G267 is a fixed-order phenomenon, not a production mechanism. For the actual adjacent-rank alignment

```text
A_r = p J_r - B_r,
J_r = sum_t W_G(t) R_r(t),
B_r = n^2 C(n,r) C(n,r-1), r in {5,6},
```

the complete characteristic-zero antipodal contribution is far below the sponsor requirement at both ranks. Production positivity must be carried by characteristic-p wraparound excess, not by the Lam-Leung/Wick pairing floor.

## Exact constrained pairing count

Move every negative term into the dyadic group by antipodal negation:

```text
2y - z = sum A - sum B
iff
y + y + B + (-z) + (-A) = 0.
```

At length `2r+2<n`, the prime-power vanishing-sum classification reduces the characteristic-zero sum to antipodal pairs. For one pair `{x,-x}`, record B-membership by `X`, A-membership by `Y`, and the oriented occupancy imbalance. Enumerating the 16 local bit patterns gives

```text
P0 = 1 + Y^2 + 2XY + X^2 + X^2Y^2,
P1 = X + Y + XY^2 + X^2Y,
P2 = XY,
P_{-d}=P_d.
```

Fixing `y`, either `z=y`, or `z` lies in one of the other `m-1` antipodal pairs in one of two orientations. Therefore, for `m=n/2`,

```text
J_r^0 = n [X^(r-1)Y^r]
  (P1 P0^(m-1) + 2(m-1) P2 P1 P0^(m-2)).
```

Exact coefficient extraction yields

```text
J5^0 = n(m-2)(m-1)(203m^2 - 1099m + 1536)/12,
J6^0 = n(m-2)(m-1)(287m^3 - 2789m^2 + 9174m - 10160)/20.
```

The probe derives the local polynomials, checks the closed forms at `n=16,32,64,128`, and independently brute-forces the abstract antipodal condition at `n=8`, obtaining `J5^0=1552`, `J6^0=672`. In the good finite-field cell `(n,p)=(8,2969)`, the actual relation counts equal those baselines exactly.

Asymptotically,

```text
J5^0 ~ (203/192)n^5,
J6^0 ~ (287/640)n^6.
```

Since `B5 ~ n^11/(5!4!)` and `B6 ~ n^13/(6!5!)`, antipodal-only positivity starts only around

```text
p ~ n^6/3045 at rank 5,
p ~ n^7/38745 at rank 6.
```

The sponsors have exponents `5.2666...` and `5.3000...`, below both constrained thresholds.

## Kernel-checked sponsor deficits

`_G268AntipodalFloorWraparoundGap.lean` proves by closed Nat arithmetic:

```text
P1 * (2^10 J5^0) < B5,
P2 * (2^9  J5^0) < B5,
P1 * (2^36 J6^0) < B6,
P2 * (2^35 J6^0) < B6.
```

Equivalently, any relation count reaching `A_r>=0` must exceed those multiples of the complete antipodal baseline. The sharper probe ratios are:

```text
B5/(P1 J5^0) = 1377.439738...,
B5/(P2 J5^0) =  688.719869...,
B6/(P1 J6^0) = 116236924227.57...,
B6/(P2 J6^0) =  58118462113.78....
```

This is direct characteristic-p structure: wraparound is not a perturbation. It must dominate the entire characteristic-zero supply, even at rank five.

## Cross-scale exact census correction

An orbit-compressed exact scan of all admissible primes gives the last observed joint-negative `tau=(p-1)/n^2` values:

```text
n=8:  1.75       through tau 128
n=16: 12.25      through tau 128
n=32: 69.09375   through tau 128
n=64: 61.921875  through tau 64
```

At `n=128`, negatives still reach the scan boundary `tau=15.703125` through tau 16. The Lean file records the exact order-32 witness

```text
p=70753, tau=69.09375,
A5=+132970510400,
A6=-1324791182208.
```

Thus G267's numerical `n=8` cutoff is not scale-free. The finite tails are consistent with FS15-FS18: fixed-depth good primes eventually recover the pairing regime, but their resultant envelope is not uniform at the sponsor scaling.

## FS15-FS18 integration

- FS15 gives Wick control only on a depth-specific good-prime set.
- FS16 proves the sharp resultant envelope `(2r)^(n/2)`, which is exponential in `n` and does not select either polynomial-size sponsor.
- FS17 unions finitely many depths but does not repair the quantifier mismatch.
- FS18 completes the characteristic-zero pairing taxonomy on that good set.
- G64/G262 force the rank-six sponsors into the exceptional wraparound regime.
- G268 adds the constrained adjacent-rank arithmetic: even at rank five, where raw Wick lies above DC, the full lawful antipodal alignment floor is still at least 512-fold too small. The production sign must come from the labelled wraparound excess itself.

## Honest boundary

The local transfer derivation and finite-field cells are exact reproducible computations. The Lean file does not formalize the finite-set bijection from alignment tuples to the coefficient formula. It kernel-checks the production formulas, deficits, universal count consumers, and exact late-negative record. This is a theorem-level arithmetic no-go and a precise formalization handoff, not the missing positive sponsor covariance estimate. CORE remains open / on BGK.
