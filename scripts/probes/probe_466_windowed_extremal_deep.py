#!/usr/bin/env python3
"""probe_466_windowed_extremal_deep.py -- deep-search companion to
probe_466_windowed_extremal.py: at n=8,k=2,a=4 (Johnson boundary) the main
probe found worst-u0 bad count == 9 for EVERY eligible direction at both
primes.  Here we throw a 10x deeper randomized search (many restarts,
annealed hill-climb, chain seeds, block designs) at a few decision-critical
directions to see if 9 is beatable, and we dissect a witness (which 4-subsets
fire, gamma multiplicities).  Also re-checks a=3 ceiling C(8,3)=56."""
import sys
import time

import numpy as np

sys.path.insert(0, 'scripts/probes')
from probe_466_windowed_extremal import (Setting, chained_u0, least_prime_1mod)


def deep_search(st, pack, a, rng, restarts=40, rounds=25, batch=384, nchain=128):
    best_c, best_u = -1, None
    for rs in range(restarts):
        # seed: fresh chain or random
        if rs % 2 == 0:
            u = chained_u0(st, pack['u1'], a, rng)
        else:
            u = rng.integers(0, st.q, size=st.n).astype(np.int64)
        c = int(st.badcounts(u[None, :], pack, [a])[a][0])
        stall = 0
        while stall < 4:
            cands = [u]
            for _ in range(batch):
                m = u.copy()
                for _ in range(int(rng.integers(1, 4))):
                    m[int(rng.integers(st.n))] = int(rng.integers(st.q))
                cands.append(m)
            for _ in range(nchain):
                cands.append(chained_u0(st, pack['u1'], a, rng))
            cnt = st.badcounts(np.array(cands), pack, [a])[a]
            i = int(cnt.argmax())
            if int(cnt[i]) > c:
                c, u = int(cnt[i]), cands[i].copy()
                stall = 0
            else:
                stall += 1
        if c > best_c:
            best_c, best_u = c, u.copy()
    return best_c, best_u


def dissect(st, u0, pack, a):
    """List bad gammas and which 4-subsets fire for each."""
    q, n = st.q, st.n
    U = u0[None, :].astype(np.int64) % q
    UT = U[:, st.Tidx]
    Pv = np.einsum('ptl,npt->npl', st.C, UT) % q
    A = (U[:, None, :] - Pv) % q
    Bz = (pack['B'] == 0)[None]
    base = ((A == 0) & Bz).sum(axis=2)[0]
    prod = ((q - A) % q) * pack['Binv'][None] % q
    gamma = np.where(pack['valid'][None], prod, q)[0]
    hits = {}
    for p in range(st.P):
        need = a - int(base[p])
        vals, cnts = np.unique(gamma[p][gamma[p] < q], return_counts=True)
        for v, c in zip(vals, cnts):
            if c >= need:
                hits.setdefault(int(v), []).append(tuple(int(x) for x in st.Tidx[p]))
    return hits


def main():
    rng = np.random.default_rng(777)
    q = least_prime_1mod(8, 8 ** 4 // 2 * 2)  # = 4129 (n^4=4096)
    q = least_prime_1mod(8, 4096)
    st = Setting(8, 2, q)
    print(f"deep search n=8 k=2 q={q} a=4 (and a=3 ceiling check)", flush=True)

    dirs = {
        'mono_j2': st.mono(2),
        'mono_j7': st.mono(7),
        'sp2_0_2_c1': (st.mono(0) + st.mono(2)) % q,
        'sp2_2_5_c1': (st.mono(2) + st.mono(5)) % q,
        'twist_2': st.mono(2) * (st.xs + 1) % q,
        'rand_dense': rng.integers(0, q, size=8).astype(np.int64),
    }
    results = {}
    for lab, u1 in dirs.items():
        pack = st.pack(u1)
        if pack['agreemax'] >= 4:
            print(f"{lab}: DEGENERATE (agreemax={pack['agreemax']}), skip", flush=True)
            continue
        t0 = time.time()
        c4, u4 = deep_search(st, pack, 4, rng)
        br = st.brute_count(u4, u1, 4)
        assert br == c4, f"{lab}: fast {c4} != brute {br}"
        c3 = int(st.badcounts(u4[None, :], pack, [3])[3][0])
        results[lab] = c4
        print(f"{lab:14s} deep worst a=4: {c4} (brute-verified)  "
              f"[{time.time()-t0:.0f}s]  (same u0 at a=3: {c3})", flush=True)
        if lab in ('mono_j2', 'sp2_2_5_c1'):
            hits = dissect(st, u4, pack, 4)
            print(f"  witness u0={u4.tolist()}")
            for g, subs in sorted(hits.items()):
                print(f"    gamma={g}: firing 4-sets {subs}")
    print("\nDEEP-SEARCH SUMMARY (a=4, q=%d): %s" % (q, results), flush=True)
    mx = max(results.values())
    mono_mx = max(v for k, v in results.items() if k.startswith('mono'))
    spread_mx = max(v for k, v in results.items() if not k.startswith('mono'))
    print(f"max monomial={mono_mx}, max spread={spread_mx} -> "
          f"{'SPREAD WINS' if spread_mx > mono_mx else ('TIE' if spread_mx == mono_mx else 'MONO WINS')}",
          flush=True)


if __name__ == '__main__':
    main()
