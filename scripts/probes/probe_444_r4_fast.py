"""
FAST all-lines census for #444 deep-band (r general), one pass over subsets.

For each (r+1)-subset S={s_0..s_r} of mu_n, the unique deg<=r interpolant of value vector v
has its two TOP coefficients (deg r and deg r-1) as fixed linear functionals of v:
  deg-r  (leading)   : T(v)  = sum_i v_i / w_i,           w_i = prod_{j!=i}(s_i - s_j)
  deg-(r-1)          : U(v)  = sum_i v_i * (-(sigma1 - s_i)) / w_i,  sigma1 = sum of nodes
So with wt_top[i]=1/w_i and wt_sub[i]=-(sigma1 - s_i)/w_i, the band coeffs for line (e,f) are:
  c0[r]   = sum_i pe[i]*wt_top[i]      c0[r-1] = sum_i pe[i]*wt_sub[i]
  c1[r]   = sum_i pf[i]*wt_top[i]      c1[r-1] = sum_i pf[i]*wt_sub[i]
gamma bad iff the two j in {r-1,r} give a consistent gamma = -c0[j]/c1[j].

This lets us evaluate ALL (e,f) lines for a single S cheaply, accumulating per-line bad sets.
Memory: per line we store the set of distinct gamma. n=32 has ~992 ordered lines; we restrict
to f<e (swap symmetry gamma->1/gamma gives identical #bad,O_P) -> ~496 lines, and the heavy
cost is C(n,r+1) subsets * (r+1) work + per-line dot products.

Validated against probe_444_r4_truemax (Gaussian-elim) on n=16.
"""
import itertools
from math import comb, gcd
from collections import defaultdict
import sys
sys.path.insert(0, 'scripts/probes')
from probe_444_r4_truemax import w_of_order, p

def census_all_lines(n, r, lines):
    """lines: list of (e,f). Returns dict line->(nz_set, has_zero)."""
    a0 = r + 1
    w = w_of_order(n)
    mu = [pow(w, i, p) for i in range(n)]
    # precompute x^e for all needed exponents
    exps = sorted({e for (e, f) in lines} | {f for (e, f) in lines})
    powtab = {ex: [pow(x, ex, p) for x in mu] for ex in exps}
    bad = {ln: dict() for ln in lines}   # line -> {gamma: example}
    zero = {ln: False for ln in lines}
    cnt = 0
    for Sidx in itertools.combinations(range(n), a0):
        s = [mu[i] for i in Sidx]
        # w_i = prod_{j!=i}(s_i - s_j)
        wt_top = [0] * a0
        sigma1 = 0
        for v in s:
            sigma1 = (sigma1 + v) % p
        ok = True
        winv = [0] * a0
        for i in range(a0):
            wi = 1
            for j in range(a0):
                if j != i:
                    wi = wi * (s[i] - s[j]) % p
            if wi == 0:
                ok = False
                break
            winv[i] = pow(wi, p - 2, p)
        if not ok:
            continue
        wt_top = winv
        wt_sub = [(-(sigma1 - s[i]) % p) * winv[i] % p for i in range(a0)]
        # for each line compute band coeffs
        for (e, f) in lines:
            pe = powtab[e]; pf = powtab[f]
            ve = [pe[i] for i in Sidx]
            vf = [pf[i] for i in Sidx]
            c0_top = 0; c0_sub = 0; c1_top = 0; c1_sub = 0
            for i in range(a0):
                c0_top = (c0_top + ve[i] * wt_top[i]) % p
                c0_sub = (c0_sub + ve[i] * wt_sub[i]) % p
                c1_top = (c1_top + vf[i] * wt_top[i]) % p
                c1_sub = (c1_sub + vf[i] * wt_sub[i]) % p
            # band j in {r-1 (sub), r (top)}
            gam = None; nd = False; consistent = True
            for (x0, x1) in [(c0_sub, c1_sub), (c0_top, c1_top)]:
                if x0 or x1:
                    nd = True
                if x1 == 0:
                    if x0:
                        consistent = False; break
                else:
                    g_ = (-x0 * pow(x1, p - 2, p)) % p
                    if gam is None:
                        gam = g_
                    elif gam != g_:
                        consistent = False; break
            if not consistent or not nd:
                continue
            if gam is None:
                continue
            if gam == 0:
                zero[(e, f)] = True
            else:
                if gam not in bad[(e, f)]:
                    bad[(e, f)][gam] = Sidx
    # finalize: O_P per line
    out = {}
    for (e, f) in lines:
        nz = list(bad[(e, f)].keys())
        mult = pow(w, (e - f) % n, p)
        rem = set(nz); orbs = 0
        while rem:
            x0 = next(iter(rem)); cur = x0; o = set()
            for _ in range(n):
                o.add(cur); cur = cur * mult % p
            orbs += 1; rem -= o
        out[(e, f)] = (len(nz), zero[(e, f)], orbs)
    return out

def validate_against_slow(n, r):
    """Cross-check fast engine vs Gaussian-elim on a few lines."""
    from probe_444_r4_truemax import census_line
    w = w_of_order(n); mu = [pow(w, i, p) for i in range(n)]
    test_lines = [(n // 2, n // 2 - 1), (n // 2, n // 2 - 3), (8, 5) if n == 16 else (16, 13)]
    fast = census_all_lines(n, r, test_lines)
    print(f"--- VALIDATE fast vs slow, n={n} r={r} ---")
    allok = True
    for ln in test_lines:
        nz_s, zb_s, op_s, K, _ = census_line(n, r, ln[0], ln[1], mu)
        nz_f, zb_f, op_f = fast[ln]
        ok = (nz_s == nz_f and zb_s == zb_f and op_s == op_f)
        allok = allok and ok
        print(f"  line {ln}: slow(#bad={nz_s},z={int(zb_s)},O_P={op_s}) "
              f"fast(#bad={nz_f},z={int(zb_f)},O_P={op_f}) OK={ok}")
    return allok

if __name__ == "__main__":
    import time
    # validate at r=3 and r=4 on n=16
    assert validate_against_slow(16, 3), "r3 validation failed"
    assert validate_against_slow(16, 4), "r4 validation failed"
    print("FAST ENGINE VALIDATED.")
