#!/usr/bin/env python3
"""
G209 — pure-ℕ extremal engine behind the depth-2 cross-orbit tail floor (#466, #509).

Context. On the deep dyadic wall (G88's cross-orbit Parseval identity #505), the
depth-2 kernel-class ℓ²-profile is `(S₀, (S_γ)_γ)`.  Opus-core landed the exact
ceiling S₀ = n (`repRF g n 2 0 = n`, G182) and, on the CORE object, established that
every occupied cross-orbit class carries mass `S_γ = n·k_γ` with `k_γ ≥ 1` integer and
`Σ_γ k_γ = n − 1` (a partition of n − 1), with the number of occupied classes capped by
the d ↦ n − d involution at `t ≤ m = n/2`.  Opus-core's own probe note flagged that the
naive floor `n²(n − 1)` (all-ones partition, t = n − 1) is NOT realized — the true floor
is strictly larger — leaving the exact extremal constant open.

This script isolates and verifies the pure-ℕ optimization fact that pins that constant,
with NO CORE-object dependency (deconflicted from opus-core's Lean tail-floor surface):

    min { Σ_i k_i²  :  k_i ≥ 1 integer,  Σ_i k_i = n − 1,  #parts ≤ n/2 }  =  2n − 3,

hence  Σ_γ S_γ² = n²·Σ k_γ²  ≥  n²(2n − 3),  the realized depth-2 cross-orbit tail floor.

Mechanism (the clean, tight, Lean-provable engine):
  (i)  pointwise  k² ≥ 3k − 2  for every integer k ≥ 1   [ ⇔ (k−1)(k−2) ≥ 0 ];
  (ii) sum over t ≤ m = n/2 parts:  Σ k² ≥ 3·Σk − 2t = 3(n−1) − 2t ≥ 3(n−1) − 2m = 2n − 3.
Tightness: the flat partition [2,…,2,1] (m−1 twos + one 1) saturates BOTH (i) — every part
lies in {1,2}, the exact equality set of (k−1)(k−2)=0 — AND the cap t = m.  So the floor
needs the class-count cap; without it (t ≤ n−1) the pointwise bound only gives n−1, which
is exactly the non-realized naive floor.

Fable's g208 tail-upper probe (2026-07-11 18:30 MDT, tip d869516e4a) showed this floor is typical
in sampled large-prime bands, but its G209 follow-up found large exceptional n=32 primes and
retracted the stronger eventual-threshold interpretation. G209 supplies the axiom-clean pure-ℕ
lower half; G210 proves the exact per-prime equality certificate.
"""

def min_sumsq(total, tmax):
    """Exact min of Σk² over partitions of `total` into t ≤ tmax positive parts."""
    best = None; bestpart = None
    for t in range(1, tmax + 1):
        if t > total:
            break
        q, r = divmod(total, t)               # flattest partition into exactly t parts
        s = r * (q + 1) ** 2 + (t - r) * q ** 2
        if best is None or s < best:
            best = s; bestpart = [q + 1] * r + [q] * (t - r)
    return best, bestpart


def check(n):
    assert n >= 2 and n % 2 == 0
    m = n // 2
    total = n - 1
    s, part = min_sumsq(total, m)
    target = 2 * n - 3
    # engine identity: 3(n-1) - 2m == 2n-3
    engine = 3 * (n - 1) - 2 * m
    # tight witness
    wit = [2] * (m - 1) + [1]
    wit_ok = (len(wit) == m and sum(wit) == total
              and sum(k * k for k in wit) == target
              and all(k * k == 3 * k - 2 for k in wit))
    tail2 = n * n * s
    return dict(n=n, m=m, total=total, min_sumsq=s, part=part, target=target,
                engine=engine, match=(s == target == engine),
                witness_tight=wit_ok, tail2=tail2, tail2_target=n * n * target)


if __name__ == "__main__":
    print("k^2 >= 3k-2 pointwise (equality iff k in {1,2}):")
    for k in range(1, 7):
        print(f"  k={k}: k^2-(3k-2) = {k*k-(3*k-2)}  {'(equality)' if k*k==3*k-2 else ''}")
    print()
    allok = True
    for n in [4, 8, 16, 32, 64, 128, 256]:
        r = check(n)
        allok &= r["match"] and r["witness_tight"]
        print(f"n={r['n']:>3} m={r['m']:>3}: min Σk² = {r['min_sumsq']:>4} "
              f"= 3(n-1)-2m = {r['engine']:>4} = 2n-3 = {r['target']:>4}  "
              f"match={r['match']}  tight_witness={r['witness_tight']}  "
              f"| tail2 = n²·Σk² = {r['tail2']} = n²(2n-3) = {r['tail2_target']}")
    print()
    # a couple of non-flat partitions to confirm the bound is a genuine floor (strict when non-flat)
    for n, ks in [(16, [8, 2, 1, 1, 1, 1, 1]), (32, [15, 5, 3, 3, 2, 1, 1, 1])]:
        assert sum(ks) == n - 1 and len(ks) <= n // 2
        ss = sum(k * k for k in ks)
        print(f"non-flat n={n} ks(len={len(ks)},sum={sum(ks)}): Σk²={ss} >= 2n-3={2*n-3} : {ss >= 2*n-3}")
    print()
    print("ALL PASS" if allok else "FAIL")
