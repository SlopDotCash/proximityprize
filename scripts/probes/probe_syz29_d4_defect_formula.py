#!/usr/bin/env python3
"""
SYZ29 part (ii): the exact D>=4 deficiency defect formula + the over-budget => d=0 arithmetic.

SYZ27 observed D>=4 over-budget band covers are deficiency-free (d=0) in tens of thousands of
trials.  SYZ28 proved the D=3 formula
    d = max(0, (n+k) - min over pairings (|Ci u Cj| + |C_l|))
which is the m=2 case of the general PARTITION-ENVELOPE formula:
    envelope_count(P) = sum over blocks B of (|union_{i in B} C_i| - k)
    d_formula        = max(0, (n-k) - min over set-partitions P of envelope_count(P)).
(A_i + A_j <= A_{Ci u Cj}, so the joint span sits inside the block envelope; dim A_{union B}
= |union B| - k over EVERY field for an MDS/RS core.  Hence d_formula is a field-independent
LOWER bound on the true deficiency -- the '>=' direction -- and the probe tests exactness '=').

This probe:
  (1) tests d == d_formula for D in {3,4,5} over random band full covers (all fields);
  (2) for D>=4 over-budget band covers, confirms min_P envelope_count(P) >= n-k (=> d_formula=0)
      and reports the MINIMIZING partition -- to expose which partition the arithmetic must kill;
  (3) the arithmetic reduction target: over-budget + band + full-cover => envelope_count(P) >= n-k
      for EVERY partition P.  We check this per-partition and find the tightest slack.
"""
import itertools, random
from probe_syz28_d3_coplanar_crack import (deficiency, sum_excess, band_sizes)

PRIMES = (101, 1009, 65537)  # field-independence over three primes; heavy 2^31 dropped for speed

def set_partitions(items):
    """All set-partitions of a list, each as a list of blocks (lists of indices)."""
    if len(items) == 1:
        yield [items]; return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i+1:]
        yield [[first]] + p

def envelope_count(cores, k, P):
    S = [set(c) for c in cores]
    tot = 0
    for block in P:
        u = set().union(*[S[i] for i in block])
        tot += len(u) - k
    return tot

def min_envelope(cores, k, n):
    idx = list(range(len(cores)))
    best = None; argmin = None
    for P in set_partitions(idx):
        v = envelope_count(cores, k, P)
        if best is None or v < best:
            best = v; argmin = P
    return best, argmin

def d_formula(cores, k, n):
    best, _ = min_envelope(cores, k, n)
    return max(0, (n - k) - best)

def test_formula(n, D, trials=30000, seed=1):
    random.seed(seed * 100 + D); k = n // 2; alpha = list(range(n)); pts = list(range(n))
    sizes = band_sizes(n)
    ceil23 = -((-2 * n) // 3)
    if ceil23 not in sizes: sizes = sizes + [ceil23]
    if not sizes: return None
    agree = 0; tested = 0; mism = []
    over_dpos = 0; over_tested = 0
    min_slack = None  # min over trials/partitions of (envelope_count - (n-k)) for over-budget
    for _ in range(trials):
        cores = []; seen = set(); ok = True
        for _c in range(D):
            s = random.choice(sizes)
            C = tuple(sorted(random.sample(pts, s)))
            if C in seen: ok = False; break
            seen.add(C); cores.append(list(C))
        if not ok: continue
        U = set().union(*[set(c) for c in cores])
        if len(U) < n: continue
        tested += 1
        # field-independent check: compute d over all primes
        ds = [deficiency(alpha, k, p, cores)[0] for p in PRIMES]
        d = ds[0]
        fieldindep = all(x == d for x in ds)
        f = d_formula(cores, k, n)
        if d == f and fieldindep: agree += 1
        else: mism.append((cores, ds, f, fieldindep))
        over = sum_excess(cores, k) >= (n - k)
        if over:
            over_tested += 1
            if d > 0: over_dpos += 1
            # tightest per-partition slack
            for P in set_partitions(list(range(D))):
                sl = envelope_count(cores, k, P) - (n - k)
                if min_slack is None or sl < min_slack: min_slack = sl
    return dict(n=n, D=D, tested=tested, agree=agree, mism=mism[:5], nmis=len(mism),
                over_tested=over_tested, over_dpos=over_dpos, min_slack=min_slack)

if __name__ == "__main__":
    print("=== SYZ29 (ii): partition-envelope defect formula d == max(0,(n-k)-min_P env(P)) ===")
    for n in (16, 20, 24):
        for D in (3, 4, 5):
            r = test_formula(n, D, trials=4000)
            if r is None: continue
            print(f"n={n:2d} D={D}: tested={r['tested']:5d} formula-agree(&fieldindep)={r['agree']:5d}"
                  f"  mismatches={r['nmis']:3d} | over-budget: tested={r['over_tested']:5d} "
                  f"d>0={r['over_dpos']:3d} min(env-(n-k))={r['min_slack']}")
            for (cores, ds, f, fi) in r['mism']:
                print("   MISMATCH d(primes)=", ds, "formula=", f, "fieldindep=", fi, "cores=", cores)
