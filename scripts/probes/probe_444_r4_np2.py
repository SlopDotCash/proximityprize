"""
INVERSE-FREE numpy census. Avoids per-element modular inverse inside the subset loop by:
  - consistency / agreement test via CROSS-MULTIPLICATION:
       band valid requires for each j: (c1_j==0 -> c0_j==0).
       both-nonzero bands agree iff c0_top*c1_sub == c0_sub*c1_top (mod p)  [g_top==g_sub]
  - gamma KEY stored as the canonical pair: use whichever band has c1!=0; store (c0_b, c1_b)
    normalized to (c0_b * inv(c1_b)) ONLY at the very end (few distinct, cheap), OR store the
    projective key (c0_b : c1_b) up to scale. Since gamma=-c0/c1 is a single field value, two
    bad (c0,c1) give same gamma iff c0*c1' == c0'*c1. We can't cheaply dedup projective pairs
    with numpy ints across subsets, so instead we compute gamma via ONE batched inverse over
    only the bad entries found this subset (typically tiny) -> few pow calls.
Math identical to validated engines; revalidated below.
"""
import numpy as np
import itertools
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_fast import w_of_order
p = 2013265921

def census_np2(n, r, lines, collect_orbit=True, progress=False):
    a0 = r + 1
    w = w_of_order(n)
    mu = np.array([pow(w, i, p) for i in range(n)], dtype=np.int64)
    L = len(lines)
    e_arr = [e for (e, f) in lines]
    f_arr = [f for (e, f) in lines]
    exps = sorted(set(e_arr) | set(f_arr))
    POW = {ex: np.array([pow(int(mu[i]), ex, p) for i in range(n)], dtype=np.int64) for ex in exps}
    PE = np.stack([POW[e] for e in e_arr])   # (L,n)
    PF = np.stack([POW[f] for f in f_arr])
    badsets = [set() for _ in range(L)]
    zero = np.zeros(L, dtype=bool)
    total = comb(n, a0)
    cc = 0
    for Sidx in itertools.combinations(range(n), a0):
        cc += 1
        if progress and cc % 20000 == 0:
            print(f"   ...{cc}/{total}", flush=True)
        S = list(Sidx)
        s = mu[S]
        sigma1 = int(s.sum() % p)
        ok = True
        winv = np.zeros(a0, dtype=np.int64)
        for i in range(a0):
            wi = 1; si = int(s[i])
            for j in range(a0):
                if j != i:
                    wi = wi * ((si - int(s[j])) % p) % p
            if wi == 0:
                ok = False; break
            winv[i] = pow(wi, p - 2, p)
        if not ok:
            continue
        wt_top = winv
        wt_sub = np.array([(-(sigma1 - int(s[i])) % p) * int(winv[i]) % p for i in range(a0)],
                          dtype=np.int64)
        Ee = PE[:, S]; Ff = PF[:, S]
        c0_top = (Ee * wt_top % p).sum(1) % p
        c0_sub = (Ee * wt_sub % p).sum(1) % p
        c1_top = (Ff * wt_top % p).sum(1) % p
        c1_sub = (Ff * wt_sub % p).sum(1) % p
        nd = (c0_top | c0_sub | c1_top | c1_sub) != 0
        top_zero = c1_top == 0
        sub_zero = c1_sub == 0
        top_ok = np.where(top_zero, c0_top == 0, True)
        sub_ok = np.where(sub_zero, c0_sub == 0, True)
        both_nz = (~top_zero) & (~sub_zero)
        # agreement via cross-mult (no inverse)
        agree = (c0_top * c1_sub - c0_sub * c1_top) % p == 0
        consistent = top_ok & sub_ok & nd & np.where(both_nz, agree, True)
        # pick band with nonzero c1 to define gamma numerator/denominator
        use_top = ~top_zero
        num = np.where(use_top, c0_top, c0_sub)   # c0 of chosen band
        den = np.where(use_top, c1_top, c1_sub)   # c1 of chosen band (nonzero where consistent&den!=0)
        idxs = np.nonzero(consistent)[0]
        if idxs.size == 0:
            continue
        dd = den[idxs]
        nn = num[idxs]
        # gamma = -nn/dd ; where dd==0 -> gamma=0 (num must be 0 too by consistency)
        for k in range(idxs.size):
            li = int(idxs[k]); d_ = int(dd[k]); n_ = int(nn[k])
            if d_ == 0:
                zero[li] = True
            else:
                gv = (-n_ * pow(d_, p - 2, p)) % p
                if gv == 0:
                    zero[li] = True
                else:
                    badsets[li].add(gv)
    out = {}
    for li, (e, f) in enumerate(lines):
        nz = badsets[li]
        if collect_orbit:
            mult = pow(w, (e - f) % n, p)
            rem = set(nz); orbs = 0
            while rem:
                x0 = next(iter(rem)); cur = x0; o = set()
                for _ in range(n):
                    o.add(cur); cur = cur * mult % p
                orbs += 1; rem -= o
        else:
            orbs = -1
        out[(e, f)] = (len(nz), bool(zero[li]), orbs)
    return out

def validate(n, r):
    from probe_444_r4_fast import census_all_lines
    test = [(n // 2, n // 2 - 1), (8, 5) if n == 16 else (16, 13), (10, 5) if n == 16 else (20, 13)]
    a = census_np2(n, r, test)
    b = census_all_lines(n, r, test)
    okall = True
    for ln in test:
        ok = a[ln] == b[ln]; okall = okall and ok
        print(f"  n={n} r={r} {ln}: np2={a[ln]} fast={b[ln]} OK={ok}")
    return okall

if __name__ == "__main__":
    import time
    assert validate(16, 3); assert validate(16, 4); assert validate(32, 4)
    print("NP2 VALIDATED")
    # quick timing on 60 lines n=32
    lines = [(e, f) for e in range(32) for f in range(e) if e and f][:60]
    t0 = time.time(); census_np2(32, 4, lines, collect_orbit=False); dt = time.time() - t0
    print(f"60 lines n=32 r=4 in {dt:.1f}s")
