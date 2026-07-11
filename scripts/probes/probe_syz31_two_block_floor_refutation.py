#!/usr/bin/env python3
"""
SYZ31: the SYZ30 two-block cross-intersection floor is FALSE, and the correcting hypothesis.

SYZ30 conjectured (probe-pinned at slack 0 by RANDOM sampling): for every two-block split of a
D>=4 over-budget band full cover, |U0 & U1| >= k.  This probe:

  (1) Exhibits an explicit counterexample (near-duplicate TRIPLE block), field-independent d=1,
      that scales to every n = 2k (strict-interior band s = floor((3n-1)/4)) -- the SYZ28 D=3
      near-duplicate PAIR crack replicated inside a D=4 cover.
  (2) Confirms via adversarial sampling that the raw floor IS violated (rare -- why SYZ30 missed).
  (3) Confirms the correcting minimal hypothesis: if some/every block carries a SPREAD PAIR
      (two cores with union >= 2s-k, i.e. overlap <= k -- no near-duplicate cluster) then the
      floor holds, with min |U0&U1| >= k+1 and zero violations.

Companion to ArkLib/.../Frontier/_SYZ31SetGeometryFacts.lean.
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import deficiency, sum_excess, band_sizes
from probe_syz29_d4_defect_formula import set_partitions


def build_crack(n):
    """Strict-interior band D=4 near-duplicate-triple crack at n=2k."""
    k = n // 2
    s = (3 * n - 1) // 4
    while not (3 * s > 2 * n and 4 * s < 3 * n):
        s -= 1
    C0 = set(range(s))
    ext = set(range(s, n))
    e = len(ext)
    base_int = list(range(s - e))
    C1 = ext | set(base_int)
    fresh = list(range(s - e, s))
    C2 = (C1 - {base_int[-1]}) | {fresh[0]}
    C3 = (C1 - {base_int[-2]}) | {fresh[0]}
    return [sorted(C0), sorted(C1), sorted(C2), sorted(C3)], k, s


def two_block_min_I(cores):
    S = [set(c) for c in cores]
    worst = 10 ** 9
    for P in set_partitions(list(range(len(cores)))):
        if len(P) != 2:
            continue
        U0 = set().union(*[S[i] for i in P[0]])
        U1 = set().union(*[S[i] for i in P[1]])
        worst = min(worst, len(U0 & U1))
    return worst


def pairwise_ok(cores, k):
    S = [set(c) for c in cores]
    return all(len(S[i] & S[j]) <= k for i, j in itertools.combinations(range(len(S)), 2))


if __name__ == "__main__":
    print("=== (1) explicit near-duplicate-triple crack, all n ===")
    for n in (16, 20, 24, 28, 32):
        cores, k, s = build_crack(n)
        U = set().union(*map(set, cores))
        I = two_block_min_I(cores)
        d = deficiency(list(range(n)), k, 101, cores)[0]
        print(f"n={n:2d} s={s} cover={len(U) == n} minI={I} k={k}  floor_holds={I >= k}  d={d}")

    print("=== (2)/(3) random adversarial: raw floor vs spread-pair-restricted ===")
    for n in (16, 20, 24):
        k = n // 2
        pts = list(range(n))
        sizes = band_sizes(n)
        ceil23 = -((-2 * n) // 3)
        if ceil23 not in sizes:
            sizes = sizes + [ceil23]
        random.seed(3)
        tested = viol = minI = 0
        minI = 10 ** 9
        minI_pw = 10 ** 9
        viol_pw = 0
        for _ in range(60000):
            for D in (4, 5):
                cores = []
                seen = set()
                ok = True
                for _c in range(D):
                    ss = random.choice(sizes)
                    C = tuple(sorted(random.sample(pts, ss)))
                    if C in seen:
                        ok = False
                        break
                    seen.add(C)
                    cores.append(list(C))
                if not ok:
                    continue
                if len(set().union(*[set(c) for c in cores])) < n:
                    continue
                if sum_excess(cores, k) < (n - k):
                    continue
                tested += 1
                I = two_block_min_I(cores)
                minI = min(minI, I)
                if I < k:
                    viol += 1
                if pairwise_ok(cores, k):
                    minI_pw = min(minI_pw, I)
                    if I < k:
                        viol_pw += 1
        print(f"n={n:2d} tested={tested} raw: minI={minI} viol={viol} | "
              f"no-near-dup: minI={minI_pw} viol={viol_pw}")
