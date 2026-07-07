"""
probe_444_r4_pertypefit.py  (#444 -- can a per-type law be salvaged for r=4?)

The task asks: "If a per-type closed form exists (even if the total is messy), report it -- a
per-type law would still give a <= K bound by summation."

We have r=4 per-type O_P (canonical = count each gamma once under a CANONICAL type assignment,
e.g. the type with the MOST pairs = deepest descent, OR by min-type). Two attribution schemes:
  scheme MAXPAIR: assign each gamma to its max-pairs realizing type (deepest descent).
  scheme MINPAIR: assign each gamma to its min-pairs realizing type (the (0,5) "generic" type).
  scheme MULTI: leave overlapped gammas in every type (the SUM we already have, =99).

For a <=K-by-summation bound we only need per-type UPPER bounds, so the relevant question is:
does the per-type bad-SUBSET count (not orbit) or per-type bad_nz have a clean form?

We compute, for r=4 at n=16,32 (and reuse known totals at 64):
  - per-type bad_nz (distinct gammas, counting a multi-type gamma in EACH type it appears)
  - per-type O_P under each attribution scheme
and fit clean forms in q=n/4.

Also: confirm the DOMINANT type. For r=3 the dominant (largest-O_P) type is (0,4) all-singleton
= the "j=r+1 all-singleton" antipodal type. For r=4 it shifts to (0,5) at n=32 but (1,3) at n=16
-> the dominant antipodal type is itself n-dependent at r=4 (it is fixed = all-singleton for r=3).
"""
import itertools
from math import comb, gcd
from collections import Counter, defaultdict

p = 2013265921

def w_of_order(n):
    e = (p - 1) // n
    for c in range(2, 2000):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n // 2, p) != 1:
            return h
    raise RuntimeError

def band_gamma_idx(Sidx, pe, pf, mu, k, a0):
    pts = [mu[i] for i in Sidx]
    m = len(pts)
    def interp(vals):
        A = [[pow(pts[i], j, p) for j in range(m)] for i in range(m)]
        M = [A[i][:] + [vals[i] % p] for i in range(m)]
        for col in range(m):
            piv = next((rr for rr in range(col, m) if M[rr][col] % p != 0), None)
            if piv is None:
                return None
            M[col], M[piv] = M[piv], M[col]
            inv = pow(M[col][col], p - 2, p)
            M[col] = [(v * inv) % p for v in M[col]]
            for rr in range(m):
                if rr != col and M[rr][col] % p != 0:
                    c = M[rr][col]
                    M[rr] = [(M[rr][t] - c * M[col][t]) % p for t in range(m + 1)]
        return [M[i][m] % p for i in range(m)]
    c0 = interp([pe[i] for i in Sidx])
    c1 = interp([pf[i] for i in Sidx])
    if c0 is None or c1 is None:
        return None
    gam = None; nd = False
    for j in range(k, a0):
        x0 = c0[j]; x1 = c1[j]
        if x0 or x1:
            nd = True
        if x1 == 0:
            if x0:
                return None
        else:
            g_ = (-x0 * pow(x1, p - 2, p)) % p
            if gam is None:
                gam = g_
            elif gam != g_:
                return None
    return gam if nd else None

def antipodal_type(Sidx, n):
    h = n // 2
    Sset = set(Sidx)
    pairs = sum(1 for j in Sidx if j < h and (j + h) in Sset)
    singles = sum(1 for j in Sidx if (j + h) % n not in Sset)
    return (pairs, singles)

def census(n, r, e, f):
    mu = [pow(w_of_order(n), i, p) for i in range(n)]
    k = r - 1; a0 = r + 1
    pe = [pow(x, e, p) for x in mu]
    pf = [pow(x, f, p) for x in mu]
    mult = pow(mu[1], (e - f) % n, p)
    gamma_types = defaultdict(set)
    for Sidx in itertools.combinations(range(n), a0):
        gv = band_gamma_idx(Sidx, pe, pf, mu, k, a0)
        if gv is None or gv % p == 0:
            continue
        gamma_types[gv].add(antipodal_type(Sidx, n))
    def orbits(gset):
        rem = set(gset); o = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; orb = set()
            for _ in range(n):
                orb.add(cur); cur = cur * mult % p
            o += 1; rem -= orb
        return o
    # attribution schemes
    maxpair = defaultdict(set); minpair = defaultdict(set); multi = defaultdict(set)
    for g, ts in gamma_types.items():
        tmax = max(ts, key=lambda t: t[0])  # most pairs
        tmin = min(ts, key=lambda t: t[0])  # fewest pairs
        maxpair[tmax].add(g)
        minpair[tmin].add(g)
        for t in ts:
            multi[t].add(g)
    return {
        'mu': mu, 'orbits': orbits,
        'maxpair': {t: orbits(gs) for t, gs in maxpair.items()},
        'minpair': {t: orbits(gs) for t, gs in minpair.items()},
        'multi':   {t: orbits(gs) for t, gs in multi.items()},
        'multi_bad': {t: len(gs) for t, gs in multi.items()},
        'total': orbits(set(gamma_types.keys())),
    }

if __name__ == "__main__":
    print("="*90)
    print("r=4 per-type O_P under 3 attribution schemes (q=n/4)")
    print("  MAXPAIR=assign gamma to its deepest-descent (most-pairs) type")
    print("  MINPAIR=assign gamma to its shallowest (fewest-pairs) type")
    print("  MULTI=count in every realizing type (the inflated SUM)")
    print("="*90)
    store = {}
    for n in [16, 32]:
        c = census(n, 4, n // 2 + 2, n // 4 + 1)
        store[n] = c
        print(f"\n  n={n} q={n//4}  TOTAL O_P={c['total']}")
        print(f"    MAXPAIR: {dict(sorted(c['maxpair'].items()))} sum={sum(c['maxpair'].values())}")
        print(f"    MINPAIR: {dict(sorted(c['minpair'].items()))} sum={sum(c['minpair'].values())}")
        print(f"    MULTI  : {dict(sorted(c['multi'].items()))} sum={sum(c['multi'].values())}")

    print("\n" + "="*90)
    print("Per-type fit attempts in q (n16->q=4, n32->q=8) for MAXPAIR scheme")
    print("="*90)
    alltypes = set()
    for n in store:
        alltypes |= set(store[n]['maxpair'])
    for t in sorted(alltypes):
        v16 = store[16]['maxpair'].get(t, 0); v32 = store[32]['maxpair'].get(t, 0)
        cands = []
        for name, fn in [
            ("C(q,2)", lambda q: comb(q, 2)),
            ("C(q,3)", lambda q: comb(q, 3)),
            ("q*C(q,2)", lambda q: q * comb(q, 2)),
            ("C(q,2)-q/2", lambda q: comb(q, 2) - q // 2),
            ("q/2", lambda q: q // 2),
            ("C(q,2)+C(q,3)", lambda q: comb(q, 2) + comb(q, 3)),
            ("q*(q-1)", lambda q: q * (q - 1)),
            ("C(2q,3)/2", lambda q: comb(2*q,3)//2 if comb(2*q,3)%2==0 else -1),
            ("(q-1)^2", lambda q: (q-1)**2),
            ("1 const", lambda q: 1),
        ]:
            if fn(4) == v16 and fn(8) == v32:
                cands.append(name)
        print(f"  type {t}: O_P n16={v16} n32={v32}  matches: {cands if cands else 'NONE'}")

    print("\n" + "="*90)
    print("DOMINANT antipodal type (largest per-type O_P) by r and n:")
    print("  r=3: dominant = (0, r+1) all-singleton, FIXED across n.")
    print("  r=4: dominant = (1,3) at n=16 but (0,5) at n=32 -> SHIFTS with n.")
    print("="*90)
    for n in [16, 32]:
        c = store[n]
        dom = max(c['multi'].items(), key=lambda kv: kv[1])
        print(f"  r=4 n={n}: dominant type = {dom[0]} with O_P={dom[1]}  "
              f"(all per-type: {dict(sorted(c['multi'].items()))})")
