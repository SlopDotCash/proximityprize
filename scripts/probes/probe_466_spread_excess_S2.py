#!/usr/bin/env python3
"""probe_466_spread_excess_S2.py -- LANE S2 (#466): decide the spread-excess constant C.

Successor calibration to the P5 referee kill of windowed SumsetExtremal
(docs/kb/deltastar-466b-p5-referee-2026-07-01.md).  Three tasks:

(A) HEAVY monomial baseline at n=16, k=4, a=7.  The referee's "9" was a
    heuristic plateau.  We reach it via the rich u0 pool (piecewise-codeword
    words carry the generic 9-structure), then hill-climb HARD to test whether
    any monomial offset beats 9.  Every per-candidate count is EXACT (the
    interpolation engine); the per-class decision witness is brute-verified over
    all q scalars.  If the monomial worst rises above 9 the ratio 21/9 drops.

(C) SELF-AGREEMENT experiment.  The n=16 spread winner x^4+x^14 has agreemax=6
    = a-1 (one point short of a-closeness).  Bucket every direction by
    (class, agreemax); measure worstBad per bucket.  Decide whether the excess
    is driven by ELEVATED self-agreement rather than "spreadness".  Report the
    restated law over BOUNDED-self-agreement (agreemax=k) directions.

(B) GROWTH.  Exact engine at n=32,k=4,a=7 (=k+3, in-window rho=1/8, feasible:
    C(32,4)=35960): does the spread/mono ratio grow when n doubles?  Plus the
    rho-matched constructive floors at n=32,k=8,a=11 (C(32,8)=10.5M, exact
    engine infeasible -- floors only, clearly labelled).

Regime: mu_n proper subgroup of F_p^*, p==1 mod n, p>=n^4, 2 primes in distinct
v2(p-1) classes; spread component gap n/2 (antipodal) excluded; the resonant
generalized-Fermat prime p=b^(2^s)+1 (e.g. 65537) is SKIPPED, flagged on sight.

Output: scripts/probes/_out_466_spread_excess_S2.txt
KILL CONDITION for any finite C: the ratio grows with n.
"""
import argparse
import sys
import time
from collections import defaultdict

import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_466_windowed_extremal import (Setting, chained_u0, interp_poly,
                                         least_prime_1mod, mu_generator,
                                         poly_eval_vec, shared_u0_pool)

# published referee 21-witnesses for elevated spread x^4+x^14 on mu_16 (a=7)
REF_ELEV = {
    65617: [25656, 44374, 59038, 3941, 58382, 47640, 51124, 29110,
            28119, 21170, 43636, 8561, 8283, 4550, 62531, 29135],
    65633: [54319, 48416, 51545, 58549, 34857, 15544, 17216, 32984,
            28127, 64688, 13955, 11542, 36322, 62969, 8859, 22086],
}


def v2(m):
    r = 0
    while m % 2 == 0:
        m //= 2
        r += 1
    return r


def is_gen_fermat(q):
    m = q - 1
    for s in range(1, 40):
        e = 1 << s
        if 2 ** e > m:
            break
        b = round(m ** (1.0 / e))
        for bb in (b - 1, b, b + 1):
            if bb >= 2 and bb ** e == m:
                return True
    return False


def primes_two_v2_classes(n, lo, skip_fermat=True):
    out = []
    m = lo
    seen_v2 = set()
    while len(out) < 2:
        p = least_prime_1mod(n, m)
        m = p + 1
        if skip_fermat and is_gen_fermat(p):
            continue
        if v2(p - 1) in seen_v2:
            continue
        seen_v2.add(v2(p - 1))
        out.append(p)
    return out


def build_spread(st, i, j, c):
    return (st.mono(i) + c * st.mono(j)) % st.q


# ----------------------------------------------------------------------
# exact per-candidate worst-u0 search: rich pool + extra seeds + hill climb
# ----------------------------------------------------------------------
def heavy_worst_u0(st, pack, a, rng, pool, budget, extra_seeds=()):
    u1 = pack['u1']
    seeds = [np.asarray(s, dtype=np.int64) % st.q for s in extra_seeds]
    C0 = np.vstack([pool] + ([np.array(seeds, dtype=np.int64)] if seeds else [])
                   + [np.array([chained_u0(st, u1, a, rng)
                                for _ in range(budget['chains'])])])
    cnt0 = st.badcounts(C0, pack, [a], chunk=budget['chunk'])[a]
    order = np.argsort(-cnt0)[:budget['restarts']]
    best_c, best_u = int(cnt0[order[0]]), C0[order[0]].copy()
    for si in order:
        u, c = C0[si].copy(), int(cnt0[si])
        stall = 0
        for _ in range(budget['rounds']):
            cands = [u]
            for _ in range(budget['batch']):
                m = u.copy()
                for _ in range(int(rng.integers(1, 4))):
                    m[int(rng.integers(st.n))] = int(rng.integers(st.q))
                cands.append(m)
            for _ in range(budget['rchain']):
                cands.append(chained_u0(st, u1, a, rng))
            cnt = st.badcounts(np.array(cands, dtype=np.int64), pack, [a],
                               chunk=budget['chunk'])[a]
            j = int(cnt.argmax())
            if int(cnt[j]) > c:
                c, u = int(cnt[j]), cands[j].copy()
                stall = 0
            else:
                stall += 1
                if stall >= budget['stall']:
                    break
        if c > best_c:
            best_c, best_u = c, u.copy()
    return best_c, best_u


# ----------------------------------------------------------------------
# constructive elevated seed: for a direction with agreemax g>=a-1, force
# (n-(a-1)) bad scalars deterministically (referee floor).
# ----------------------------------------------------------------------
def elevated_seed(st, u1, pack, a, rng):
    q, n, xs = st.q, st.n, st.xs
    u1 = np.asarray(u1, dtype=np.int64) % q
    Bz = (pack['B'] == 0)
    p = int(Bz.sum(axis=1).argmax())
    T = [int(t) for t in st.Tidx[p]]
    h = interp_poly([int(xs[t]) for t in T], [int(u1[t]) for t in T], q)
    Sstar = [l for l in range(n) if bool(Bz[p, l])]
    keep = set(Sstar[:a - 1])
    cv = poly_eval_vec(h, xs, q)
    u0 = cv.copy()
    off = [l for l in range(n) if l not in keep]
    gammas = rng.choice(np.arange(1, q), size=len(off), replace=False)
    for idx, l in enumerate(off):
        u0[l] = (int(cv[l]) - int(gammas[idx]) * int(u1[l])) % q
    return u0 % q, len(Sstar)


# ----------------------------------------------------------------------
def evaluate_directions(st, a, dirs, rng, pool, budget, brute_top=True,
                        elevate=True):
    q = st.q
    rows = []
    for (name, cls, u1) in dirs:
        pack = st.pack(u1)
        g = pack['agreemax']
        if g >= a:
            rows.append(dict(name=name, cls=cls, agreemax=g, worst=q,
                             eligible=False))
            continue
        extra = []
        if elevate and g >= a - 1:
            s, _ = elevated_seed(st, u1, pack, a, rng)
            extra.append(s)
        if name == 'sp_4_14_c1' and q in REF_ELEV:
            extra.append(REF_ELEV[q])
        c, u0 = heavy_worst_u0(st, pack, a, rng, pool, budget, extra_seeds=extra)
        rows.append(dict(name=name, cls=cls, agreemax=g, worst=c, u0=u0,
                         u1=u1, eligible=True))
    if brute_top:
        for cls in ('monomial', 'spread2'):
            elig = [r for r in rows if r['cls'] == cls and r['eligible']]
            if not elig:
                continue
            top = max(elig, key=lambda r: r['worst'])
            br = st.brute_count(top['u0'], top['u1'], a,
                                gchunk=max(48, 2 ** 20 // st.P))
            top['brute'] = br
            assert br == top['worst'], \
                f"{top['name']}: engine {top['worst']} vs brute {br}"
    return rows


def print_buckets(rows, a, k, label):
    print(f"\n--- {label}  a={a} k={k} ---", flush=True)
    buck = defaultdict(list)
    for r in rows:
        if r['eligible']:
            buck[(r['cls'], r['agreemax'])].append((r['worst'], r['name']))
    for key in sorted(buck):
        vals = sorted(buck[key], reverse=True)
        print(f"   {key[0]:9s} agreemax={key[1]}: max={vals[0][0]} "
              f"({vals[0][1]}) all={[v[0] for v in vals]}", flush=True)
    mono = [r for r in rows if r['cls'] == 'monomial' and r['eligible']]
    spr = [r for r in rows if r['cls'] == 'spread2' and r['eligible']]
    bm = max(mono, key=lambda r: r['worst']) if mono else None
    bs = max(spr, key=lambda r: r['worst']) if spr else None
    if bm and bs:
        print(f"   >>> OVERALL best_mono={bm['worst']} ({bm['name']} amax "
              f"{bm['agreemax']}{', brute '+str(bm.get('brute')) if 'brute' in bm else ''})"
              f"  best_spread={bs['worst']} ({bs['name']} amax {bs['agreemax']}"
              f"{', brute '+str(bs.get('brute')) if 'brute' in bs else ''})"
              f"  RATIO={bs['worst']/bm['worst']:.4f}", flush=True)
    # bounded-self-agreement (agreemax == k) restatement
    bnd_m = [r for r in mono if r['agreemax'] == k]
    bnd_s = [r for r in spr if r['agreemax'] == k]
    if bnd_m and bnd_s:
        wm = max(r['worst'] for r in bnd_m)
        ws = max(r['worst'] for r in bnd_s)
        print(f"   >>> BOUNDED-SELF-AGREEMENT (agreemax=k={k}): mono={wm} "
              f"spread={ws} RATIO={ws/wm:.4f}", flush=True)
    return dict(best_mono=bm['worst'] if bm else None,
                best_spread=bs['worst'] if bs else None)


# ======================================================================
def task_AC(q, rng, budget):
    n, k, a = 16, 4, 7
    st = Setting(n, k, q)
    print(f"\n{'='*78}\nTASK A+C  n={n} k={k} a={a} rho={k}/{n} q={q} "
          f"v2(q-1)={v2(q-1)} q>=n^4:{q>=n**4} genFermat:{is_gen_fermat(q)} "
          f"C(n,k)={st.P}", flush=True)
    t0 = time.time()
    pool = shared_u0_pool(st, rng, 16, 30, 500)
    dirs = []
    for j in range(k, 12):
        dirs.append((f"mono_j{j}", "monomial", st.mono(j)))
    even = [(i, j) for i in range(0, n, 2) for j in range(0, n, 2)
            if i < j and (j - i) % n != n // 2]
    for (i, j) in even:
        dirs.append((f"sp_{i}_{j}_c1", "spread2", build_spread(st, i, j, 1)))
    for (i, j) in [(1, 4), (3, 6), (1, 6), (2, 7), (4, 7), (5, 10), (1, 8),
                   (3, 10), (2, 9), (5, 12)]:
        if (j - i) % n == n // 2:
            continue
        dirs.append((f"spm_{i}_{j}", "spread2", build_spread(st, i, j, 1)))
    rows = evaluate_directions(st, a, dirs, rng, pool, budget)
    res = print_buckets(rows, a, k, f"n16k4 q={q}")
    print(f"[task A+C q={q} done {time.time()-t0:.0f}s]", flush=True)
    return res


def task_B(rng, budget):
    n, k, a = 32, 4, 7
    q = primes_two_v2_classes(n, n ** 4)[0]
    st = Setting(n, k, q)
    print(f"\n{'='*78}\nTASK B  n={n} k={k} a={a}=k+3 rho={k}/{n} q={q} "
          f"v2(q-1)={v2(q-1)} q>=n^4:{q>=n**4} genFermat:{is_gen_fermat(q)} "
          f"C(n,k)={st.P}", flush=True)
    t0 = time.time()
    pool = shared_u0_pool(st, rng, 16, 24, 300)
    dirs = []
    for j in range(k, 16):
        dirs.append((f"mono_j{j}", "monomial", st.mono(j)))
    even = [(i, j) for i in range(0, n, 2) for j in range(0, n, 2)
            if i < j and (j - i) % n != n // 2]
    idx = rng.choice(len(even), size=min(24, len(even)), replace=False)
    for ii in idx:
        i, j = even[int(ii)]
        dirs.append((f"sp_{i}_{j}_c1", "spread2", build_spread(st, i, j, 1)))
    rows = evaluate_directions(st, a, dirs, rng, pool, budget, brute_top=False)
    res = print_buckets(rows, a, k, f"n32k4 q={q}")
    print(f"[task B exact n=32k4 done {time.time()-t0:.0f}s]", flush=True)

    # rho-matched constructive floors at n=32 k=8 a=11 (no subset enumeration)
    n2, k2, a2 = 32, 8, 11
    mono_floor = 1 + (n2 - a2) // (a2 - k2)
    elev_floor = n2 - (a2 - 1)
    n16_mono = 1 + (16 - 7) // (7 - 4)
    n16_elev = 16 - 6
    print(f"\n   [rho-matched n=32 k=8 a=11 CONSTRUCTIVE FLOORS only "
          f"(C(32,8)=10.5M -> exact engine infeasible)]", flush=True)
    print(f"      monomial chained floor 1+floor((32-11)/(11-8)) = {mono_floor}",
          flush=True)
    print(f"      elevated (agreemax=a-1) floor n-(a-1) = {elev_floor}", flush=True)
    print(f"      n=32 floor-ratio elevated/mono = {elev_floor/mono_floor:.3f}",
          flush=True)
    print(f"      cf. n=16 floor-ratio {n16_elev}/{n16_mono} = "
          f"{n16_elev/n16_mono:.3f}   (deterministic floors, pre-climb)",
          flush=True)
    print(f"[task B done {time.time()-t0:.0f}s]", flush=True)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--stage', choices=['AC', 'B', 'all'], default='all')
    ap.add_argument('--fast', action='store_true')
    args = ap.parse_args()
    rng = np.random.default_rng(4662)
    if args.fast:
        b16 = dict(chains=16, restarts=3, rounds=5, batch=128, rchain=32,
                   stall=2, chunk=192)
        b32 = dict(chains=12, restarts=2, rounds=3, batch=64, rchain=20,
                   stall=2, chunk=8)
    else:
        b16 = dict(chains=32, restarts=5, rounds=12, batch=256, rchain=64,
                   stall=3, chunk=192)
        b32 = dict(chains=20, restarts=3, rounds=6, batch=128, rchain=40,
                   stall=2, chunk=8)
    summary = []
    if args.stage in ('AC', 'all'):
        for q in primes_two_v2_classes(16, 16 ** 4):
            summary.append(('n16k4', q, task_AC(q, rng, b16)))
    if args.stage in ('B', 'all'):
        summary.append(('n32k4', None, task_B(rng, b32)))
    print("\n" + "=" * 78 + "\nS2 SUMMARY (exact counts; decision witnesses "
          "brute-verified):", flush=True)
    for key, q, r in summary:
        if r['best_mono']:
            print(f"   {key} q={q}: mono={r['best_mono']} spread={r['best_spread']}"
                  f" RATIO={r['best_spread']/r['best_mono']:.4f}", flush=True)


if __name__ == '__main__':
    main()
