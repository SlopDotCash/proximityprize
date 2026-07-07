"""
NUMPY-vectorized all-lines census (over lines, per subset) for #444 deep-band.
Same math as probe_444_r4_fast but vectorizes the per-line band-coefficient dot products and
the gamma consistency check across ALL lines simultaneously, using int64 mod-p arithmetic.

p=2013265921 < 2^31 so products of two residues fit in int64 (max ~4.05e18 < 9.2e18). We do
modular reduction after each multiply. Modular inverse done via pow on python ints (vectorized
through a small cache since the set of distinct c1 values per subset is small... actually we
need elementwise inverse of c1_top, c1_sub per line; do it with a fast vectorized pow).

Strategy per subset S:
  compute winv[i], wt_top[i]=winv[i], wt_sub[i]=-(sigma1-s_i)*winv[i]  (5 ints)
  For each line we need pe[S], pf[S]. Precompute POW[ex][i over n]; gather columns for S.
  Band coeffs are linear in pe,pf -> matrix form:
     c0_top = PE_S @ wt_top   (PE_S is (L x 5) for the L lines' e-exponent values on S)
  But e differs per line, so PE_S = POW[e_of_line][S].  We build arrays Ee (L,5), Ff (L,5)
  by gathering. Then c0_top = (Ee * wt_top).sum(1) % p, etc. Then gamma check vectorized.
Distinct-gamma accumulation: we keep a python set per line; update only where bad. To keep it
fast we collect (line_idx, gamma) pairs in arrays and dedup at the end.
"""
import numpy as np
import itertools
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_fast import w_of_order
p = 2013265921

def vec_inv(a):
    """elementwise modular inverse mod p of int64 array a (a may contain 0 -> returns 0)."""
    out = np.zeros_like(a)
    nz = a != 0
    vals = a[nz].tolist()
    inv = [pow(int(v), p - 2, p) for v in vals]
    out[nz] = np.array(inv, dtype=np.int64)
    return out

def mulmod(a, b):
    return (a * b) % p

def census_np(n, r, lines, collect_orbit=True):
    a0 = r + 1
    w = w_of_order(n)
    mu = np.array([pow(w, i, p) for i in range(n)], dtype=np.int64)
    L = len(lines)
    e_arr = np.array([e for (e, f) in lines], dtype=np.int64)
    f_arr = np.array([f for (e, f) in lines], dtype=np.int64)
    exps = sorted({int(x) for x in e_arr} | {int(x) for x in f_arr})
    POW = {ex: np.array([pow(int(mu[i]), ex, p) for i in range(n)], dtype=np.int64) for ex in exps}
    # POW matrix indexed by line: PE_line[l] = POW[e_arr[l]], shape (L, n)
    PE = np.stack([POW[int(e)] for e in e_arr])   # (L,n)
    PF = np.stack([POW[int(f)] for f in f_arr])   # (L,n)
    # accumulators: per-line dict gamma->1. Use list of sets.
    badsets = [set() for _ in range(L)]
    zero = np.zeros(L, dtype=bool)
    for Sidx in itertools.combinations(range(n), a0):
        S = list(Sidx)
        s = mu[S]  # (a0,)
        sigma1 = int(s.sum() % p)
        # winv
        ok = True
        winv = np.zeros(a0, dtype=np.int64)
        for i in range(a0):
            wi = 1
            si = int(s[i])
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
        # gather Ee = PE[:, S] (L, a0), Ff = PF[:, S]
        Ee = PE[:, S]   # (L,a0)
        Ff = PF[:, S]
        # band coeffs (L,)
        c0_top = (Ee * wt_top % p).sum(1) % p
        c0_sub = (Ee * wt_sub % p).sum(1) % p
        c1_top = (Ff * wt_top % p).sum(1) % p
        c1_sub = (Ff * wt_sub % p).sum(1) % p
        # nondegeneracy: at least one of the four nonzero
        nd = (c0_top | c0_sub | c1_top | c1_sub) != 0
        # consistency: for j in {sub, top}: if c1_j==0 need c0_j==0; else gamma=-c0_j/c1_j equal
        inv_top = vec_inv(c1_top)
        inv_sub = vec_inv(c1_sub)
        g_top = (-c0_top * inv_top) % p
        g_sub = (-c0_sub * inv_sub) % p
        top_zero = c1_top == 0
        sub_zero = c1_sub == 0
        # validity per band: zero branch ok iff c0==0 ; nonzero branch always gives a gamma
        top_ok = np.where(top_zero, c0_top == 0, True)
        sub_ok = np.where(sub_zero, c0_sub == 0, True)
        # determine pinned gamma: prefer nonzero-c1 band; both nonzero -> must agree
        both_nz = (~top_zero) & (~sub_zero)
        agree = (g_top == g_sub)
        consistent = top_ok & sub_ok & nd & np.where(both_nz, agree, True)
        # gamma value: if top nonzero use g_top else if sub nonzero use g_sub else gamma=0 (degenerate, but nd guaranteed nonzero coeff somewhere; if both c1 zero then c0 must be nonzero somewhere but no finite gamma -> that's the "x^e top nonzero, x^f zero" => not consistent unless c0 also zero; if all four zero nd false).
        gam = np.where(~top_zero, g_top, np.where(~sub_zero, g_sub, 0))
        idxs = np.nonzero(consistent)[0]
        for li in idxs.tolist():
            gv = int(gam[li])
            if gv == 0:
                # gamma=0 only if c0 numerator zero with c1 nonzero -> the all-zero c0 case
                zero[li] = True
            else:
                badsets[li].add(gv)
    # finalize
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
    test = [(n // 2, n // 2 - 1), (8, 5) if n == 16 else (16, 13), (10, 5) if n == 16 else (20, 15)]
    a = census_np(n, r, test)
    b = census_all_lines(n, r, test)
    okall = True
    for ln in test:
        ok = a[ln] == b[ln]
        okall = okall and ok
        print(f"  n={n} r={r} {ln}: np={a[ln]} fast={b[ln]} OK={ok}")
    return okall

if __name__ == "__main__":
    assert validate(16, 3)
    assert validate(16, 4)
    assert validate(32, 4)
    print("NP ENGINE VALIDATED")
