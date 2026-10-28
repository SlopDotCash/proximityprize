# SYZ3 five-core obstruction at the rate-half predecessor

Author: Mikhail Izhutkin (@mashingaan)

Status: exact arithmetic research result. This is a refutation of the
all-stack predecessor count hypotheses used by the conditional rate-half
reduction. It is not a Delta Star threshold closure.

The probe `scripts/probes/probe_syz3_five_core_predecessor.py` uses

```text
N = 2^30, d = 2^24, K = 2^29, Q = 2^128
P1 = N (Q + 192) + 1
P2 = N (2 Q + 13) + 1.
```

For labels modulo 64, take the common block `{0,...,30}` and five extra
pairs `{31+2j,32+2j}`. The five cores each have `33d` coordinates. The
height is `j` on the extra pair for core `j` and is `5` on all remaining
labels. Every eligible core-label slot has multiplier `a = height + j` in
`{1,...,9}`. There are `155` slots, and the probe checks that all pairs
`(label,a)` are distinct.

The polynomial witnesses use the common factor

```text
Z(Y) = product over a in {0,...,30} of (Y - omega^a), omega = g^d.
```

The two rows are `u1(i) = height(i) Z((g^i)^d)` and
`u0(i) = height(i)^2 Z((g^i)^d) g^i`. For core `j`, the codewords are
`j Z(X^d)` and `j^2 Z(X^d) X`. Their degrees are below `K`, and each
off-core coordinate supplies a nonjoint pencil witness on `33d+1` points,
which is exactly the predecessor agreement threshold.

The exact powers `a^N mod P1` and `a^N mod P2` are pairwise distinct for
`1 <= a <= 9`. Raising a scalar collision to the `N`th power therefore
separates the multiplier and then the order-`N` generator coordinate. The
resulting lower bound is

```text
155d = 2,600,468,480.
```

This exceeds the first-field `N` budget by `1,526,726,656` and the
second-field `2N` budget by `452,984,832`. Thus both universal predecessor
count hypotheses in the rate-half reduction are false for these canonical
fields. This does not refute the exact supremum or prove a new threshold.

As an independent check of the MCA nonjoint clause, the same construction is
enumerated at `N=128`, `K=64`, `P=1409`, and generator `1022`. Direct
Lagrange interpolation verifies all `310` witnesses and their distinct
scalars, exceeding `2N` by `54`. The finite check is evidence for the
construction and is not a transfer theorem.

The five-core construction itself remains an exact-arithmetic probe and is not
yet a kernel-checked Lean theorem. Separately, the existing three-core SYZ3
certificate now has an axiom-clean canonical consumer in
`Research/ProximityPrize/Frontier/_SYZ3OverBudgetStackWitness.lean`:
`firstPrime_predecessor_worstCaseIncidence_refuted` directly refutes the
first-field `WorstCaseIncidenceBounded` premise at this predecessor, and
`firstPrime_predecessor_mcaDeltaStar_le` sends the same witness through the
canonical `mcaDeltaStar` ledger. These declarations do not formalize the
five-core probe or transfer it to the second field, and they do not close the
prize.
