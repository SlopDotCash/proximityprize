"""
LEAN n=64 census for a FEW lines (the predicted maximizer family). Optimized inner loop:
 - batch modular inversion (one pow per subset instead of 5) for the winv values
 - minimal python overhead, no numpy (line count tiny)
 - gamma stored per line; O_P via orbit at the end.
Validated against np2/fast on n=16,32 below before the n=64 run.
"""
import itertools
from math import comb, gcd
import sys, time
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_fast import w_of_order
p = 2013265921

def census_lean(n, r, lines, progress=0):
    a0 = r + 1
    w = w_of_order(n)
    mu = [pow(w, i, p) for i in range(n)]
    L = len(lines)
    exps = sorted({e for e, f in lines} | {f for e, f in lines})
    POW = {ex: [pow(x, ex, p) for x in mu] for ex in exps}
    PE = [POW[e] for (e, f) in lines]
    PF = [POW[f] for (e, f) in lines]
    bad = [dict() for _ in range(L)]
    zero = [False] * L
    total = comb(n, a0)
    cc = 0
    rng = range(a0)
    for Sidx in itertools.combinations(range(n), a0):
        cc += 1
        if progress and cc % progress == 0:
            print(f"   ...{cc}/{total}", flush=True)
        s = [mu[i] for i in Sidx]
        # w_i = prod_{j!=i}(s_i-s_j); batch-invert the w_i
        wv = []
        bad_subset = False
        for i in rng:
            wi = 1; si = s[i]
            for j in rng:
                if j != i:
                    wi = wi * (si - s[j]) % p
            if wi == 0:
                bad_subset = True; break
            wv.append(wi)
        if bad_subset:
            continue
        # batch inverse of wv (all nonzero)
        pref = [1] * (a0 + 1)
        for i in rng:
            pref[i + 1] = pref[i] * wv[i] % p
        inv_all = pow(pref[a0], p - 2, p)
        winv = [0] * a0
        suff = 1
        for i in range(a0 - 1, -1, -1):
            winv[i] = pref[i] * suff % p * inv_all % p
            suff = suff * wv[i] % p
        sigma1 = 0
        for v in s:
            sigma1 += v
        sigma1 %= p
        wt_sub = [(-(sigma1 - s[i]) % p) * winv[i] % p for i in rng]
        for li in range(L):
            pe = PE[li]; pf = PF[li]
            c0t = c0s = c1t = c1s = 0
            for idx in range(a0):
                si = Sidx[idx]
                ve = pe[si]; vf = pf[si]
                wt = winv[idx]; ws = wt_sub[idx]
                c0t += ve * wt; c0s += ve * ws
                c1t += vf * wt; c1s += vf * ws
            c0t %= p; c0s %= p; c1t %= p; c1s %= p
            if (c0t | c0s | c1t | c1s) == 0:
                continue  # degenerate (all zero)
            # consistency
            top_zero = (c1t == 0); sub_zero = (c1s == 0)
            if top_zero and c0t != 0:
                continue
            if sub_zero and c0s != 0:
                continue
            if (not top_zero) and (not sub_zero):
                if (c0t * c1s - c0s * c1t) % p != 0:
                    continue
            # gamma from a nonzero-c1 band
            if not top_zero:
                gv = (-c0t * pow(c1t, p - 2, p)) % p
            elif not sub_zero:
                gv = (-c0s * pow(c1s, p - 2, p)) % p
            else:
                # both c1 zero, but some c0 nonzero -> handled above (continue). if c0 all zero -> degenerate
                continue
            if gv == 0:
                zero[li] = True
            else:
                bad[li][gv] = 1
    out = {}
    for li, (e, f) in enumerate(lines):
        nz = list(bad[li].keys())
        mult = pow(w, (e - f) % n, p)
        rem = set(nz); orbs = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; o = set()
            for _ in range(n):
                o.add(cur); cur = cur * mult % p
            orbs += 1; rem -= o
        out[(e, f)] = (len(nz), zero[li], orbs)
    return out

if __name__ == "__main__":
    from probe_444_r4_fast import census_all_lines
    # validate
    for n in [16, 32]:
        for r in [3, 4]:
            test = [(n // 2, n // 2 - 1), (n // 2 + 2, n // 4 + 1)]
            a = census_lean(n, r, test); b = census_all_lines(n, r, test)
            for ln in test:
                assert a[ln] == b[ln], (n, r, ln, a[ln], b[ln])
            print(f"lean OK n={n} r={r}: {[ (ln,a[ln]) for ln in test]}")
    print("LEAN VALIDATED. Running n=64 family lines...")
    n = 64; r = 4; q = n // 4; h = n // 2; t = q + 1
    fam = [(2 * t, t), (2 * t - 2, t), (h, q + 1), (h + 2, q - 1)]
    t0 = time.time()
    res = census_lean(n, r, fam, progress=1000000)
    dt = time.time() - t0
    K = (1 << r) * comb(h, r)
    print(f"n=64 r=4 family census in {dt:.0f}s, K={K}:", flush=True)
    for ln in fam:
        nz, zb, op = res[ln]
        print(f"  (x^{ln[0]},x^{ln[1]}) e-f={(ln[0]-ln[1])%n}: #bad={nz}(+{int(zb)}z) O_P={op} "
              f"n*O_P+1={n*op+1} bad/K={nz/K:.5f}", flush=True)
