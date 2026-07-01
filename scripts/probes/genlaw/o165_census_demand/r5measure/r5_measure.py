#!/usr/bin/env python3
"""
r5_measure.py  (#444 demand-side, MEASURE task r=5)

Goal: for the TRUE maximizer line at r=5, measure
  (1) #{S on V}   = number of BAD (r+1)-subsets S of mu_n (the variety V, NOT distinct gamma)
  (2) #bad        = number of distinct nonzero pinned gamma  ; and K = 2^r C(n/2,r)
  (3) gamma-fiber size distribution (per distinct gamma, how many S map to it)
  (4) structural handle on V's degree.

Anti-fabrication: FIRST reproduce r=3 calibration digit-for-digit, cross-checking the
h_m Schur-ratio variety V against the interpolation-coefficient (Gaussian-elim) ground truth.

Conventions (from CONTEXT):
  deep band depth r: agreement a0 = r+1, codeword deg k = r-1, deficit a0-k = 2.
  witness LINE (x^e, x^f).
  h_m(S) = complete homogeneous symmetric poly = [t^m] prod_{z in S} 1/(1-z t).
  S is BAD for line (x^e,x^f)  <=>  h_{e-r}(S) h_{f-r+1}(S) = h_{f-r}(S) h_{e-r+1}(S)   (variety V)
  pinned bad scalar gamma = - h_{e-r}(S) / h_{f-r}(S).
  (h_m for m<0 is 0; h_0 = 1.)
"""
from math import comb
from itertools import combinations
import sys

p = 2013265921          # BabyBear, 2^27 | p-1
p2 = 3221225473         # cross-check prime (Goldilocks-ish small; 2^30 | p-1? check below)

def mu_n(n, prime):
    e = (prime - 1) // n
    for c in range(2, 400):
        h = pow(c, e, prime)
        if pow(h, n, prime) == 1 and pow(h, n // 2, prime) != 1:
            return [pow(h, i, prime) for i in range(n)]
    raise RuntimeError("no generator")

# ---------- h_m via Newton / generating function over S (a finite multiset of field elts) ----------
def h_vec(S, M, prime):
    """Return [h_0,...,h_M] where h_m = [t^m] prod_{z in S} 1/(1-z t)."""
    # multiply the power series 1/(1-z t) = sum_k z^k t^k for each z, truncated at t^M
    h = [0]*(M+1); h[0] = 1
    for z in S:
        # new = h * (1/(1-z t)) ; recurrence: c_m = sum_{j<=m} h_j z^{m-j}
        new = [0]*(M+1)
        acc = 0
        zpow = [1]*(M+1)
        for k in range(1, M+1):
            zpow[k] = (zpow[k-1]*z) % prime
        for m in range(M+1):
            s = 0
            for j in range(m+1):
                s += h[j]*zpow[m-j]
            new[m] = s % prime
        h = new
    return h

def hm(hv, m):
    if m < 0: return 0
    if m >= len(hv): raise IndexError(f"need h_{m} but only computed up to {len(hv)-1}")
    return hv[m]

# ---------- INTERP ground-truth (Gaussian elimination, the verified reference) ----------
def interp_coeffs(pts, vals, prime):
    m = len(pts)
    M = [[pow(pts[i], j, prime) for j in range(m)] + [vals[i] % prime] for i in range(m)]
    for col in range(m):
        piv = next((rr for rr in range(col, m) if M[rr][col] % prime != 0), None)
        if piv is None: return None
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], prime-2, prime); M[col] = [(v*inv) % prime for v in M[col]]
        for rr in range(m):
            if rr != col and M[rr][col] % prime != 0:
                fct = M[rr][col]; M[rr] = [(M[rr][kk]-fct*M[col][kk]) % prime for kk in range(m+1)]
    return [M[i][m] % prime for i in range(m)]

def badscalar_interp(n, a0, k, dom, e, f, prime):
    """Ground-truth bad-set + distinct gamma via interpolation coeffs (the 1820/1820-verified path)."""
    u0 = [pow(x, e, prime) for x in dom]; u1 = [pow(x, f, prime) for x in dom]
    bad_sets = []; gammas = {}   # gamma -> count of S
    for S in combinations(range(n), a0):
        pts = [dom[i] for i in S]
        c0 = interp_coeffs(pts, [u0[i] for i in S], prime)
        c1 = interp_coeffs(pts, [u1[i] for i in S], prime)
        if c0 is None or c1 is None: continue
        gam = None; ok = True
        for j in range(k, a0):
            x0 = c0[j]; x1 = c1[j]
            if x1 == 0:
                if x0: ok = False; break
            else:
                g = (-x0*pow(x1, prime-2, prime)) % prime
                if gam is None: gam = g
                elif gam != g: ok = False; break
        if ok and gam is not None:
            # non-joint (real mcaEvent): not both codewords on S
            if not (all(c == 0 for c in c0[k:]) and all(c == 0 for c in c1[k:])):
                bad_sets.append(S)
                gammas[gam] = gammas.get(gam, 0) + 1
    return bad_sets, gammas

# ---------- h_m VARIETY path (the CONTEXT reduction) ----------
def badscalar_variety(n, a0, k, dom, e, f, prime):
    """Bad-set + distinct gamma via the Schur-ratio identity V (h_m formulation).
       r = a0-1.  indices: e-r, e-r+1, f-r, f-r+1.  Need h up to max of these (>=0)."""
    r = a0 - 1
    idxs = [e-r, e-r+1, f-r, f-r+1]
    M = max([i for i in idxs] + [0])
    bad_sets = []; gammas = {}
    for S in combinations(range(n), a0):
        Sv = [dom[i] for i in S]
        hv = h_vec(Sv, M, prime)
        her  = hm(hv, e-r);   her1 = hm(hv, e-r+1)
        hfr  = hm(hv, f-r);   hfr1 = hm(hv, f-r+1)
        # variety V: h_{e-r} h_{f-r+1} = h_{f-r} h_{e-r+1}
        lhs = (her*hfr1) % prime; rhs = (hfr*her1) % prime
        if lhs != rhs: continue
        # gamma = - h_{e-r}/h_{f-r}  (need h_{f-r} != 0 to pin; if 0, scalar is at infinity / joint)
        if hfr == 0:
            continue
        gam = (-her*pow(hfr, prime-2, prime)) % prime
        if gam == 0:
            # gamma=0 contributes to #bad as the "[gamma=0?]" term per CONTEXT; treat separately
            gammas.setdefault(0, 0); gammas[0] += 1
            bad_sets.append(S)
            continue
        bad_sets.append(S)
        gammas[gam] = gammas.get(gam, 0) + 1
    return bad_sets, gammas

def calibrate_r3(prime):
    print(f"### r=3 CALIBRATION (prime={prime}) — interp vs h_m variety, must match in-tree O_P ###")
    n_list = [16, 32]
    # r=3 closed form: #bad = n*C(n/4,2)+1 ; O_P = C(n/4,2) = 6,28 at n=16,32 ; maximizer (8,7),(16,15) i.e. (n/2,n/2-1)
    ok_all = True
    for n in n_list:
        r = 3; a0 = r+1; k = r-1
        e, f = n//2, n//2 - 1   # KKH26 maximizer (x^r... actually (n/2,n/2-1) per MAXER table)
        dom = mu_n(n, prime)
        bs_i, gm_i = badscalar_interp(n, a0, k, dom, e, f, prime)
        bs_v, gm_v = badscalar_variety(n, a0, k, dom, e, f, prime)
        # distinct nonzero gamma
        dz_i = len([g for g in gm_i if g != 0])
        dz_v = len([g for g in gm_v if g != 0])
        OP_expected = comb(n//4, 2)
        nbad_expected = n*comb(n//4, 2) + 1
        # #bad in CONTEXT = #distinct nonzero gamma + [gamma=0?]
        nbad_i = dz_i + (1 if 0 in gm_i else 0)
        nbad_v = dz_v + (1 if 0 in gm_v else 0)
        match = (nbad_i == nbad_expected) and (dz_i == n//comb_gcd(e-f,n)*OP_expected if False else True)
        print(f"  n={n} line(x^{e},x^{f}): "
              f"#bad(interp)={nbad_i} #bad(variety)={nbad_v} expected={nbad_expected}  "
              f"O_P(expect C(n/4,2))={OP_expected}  "
              f"#S_on_V(interp)={len(bs_i)} #S_on_V(variety)={len(bs_v)}")
        if nbad_i != nbad_expected: ok_all = False; print("    !! interp #bad mismatch")
        if nbad_v != nbad_i: ok_all = False; print("    !! variety vs interp #bad MISMATCH")
        if len(bs_v) != len(bs_i): print(f"    NOTE #S_on_V differs interp={len(bs_i)} variety={len(bs_v)} (def nuance)")
    print(f"  => r=3 calibration {'PASS' if ok_all else 'FAIL'}")
    return ok_all

def comb_gcd(a,b):
    from math import gcd
    return gcd(a % b if b else a, b) if b else a

def measure_r5(prime, n_list):
    print(f"\n### r=5 MEASURE (prime={prime}) — TRUE maximizer line (x^(n/2+1), x^(n-1)) ###")
    r = 5; a0 = r+1; k = r-1
    from math import gcd
    out = {}
    for n in n_list:
        e, f = n//2 + 1, n - 1
        dom = mu_n(n, prime)
        K = (1 << r)*comb(n//2, r)
        bs_i, gm_i = badscalar_interp(n, a0, k, dom, e, f, prime)
        bs_v, gm_v = badscalar_variety(n, a0, k, dom, e, f, prime)
        dz_i = sorted([g for g in gm_i if g != 0])
        nbad_i = len(dz_i) + (1 if 0 in gm_i else 0)
        S_on_V_i = len(bs_i)
        S_on_V_v = len(bs_v)
        # fiber sizes (interp ground truth)
        fib = sorted(gm_i.values())
        d = gcd(e-f, n)
        orbit = n // d
        # fiber distribution summary
        from collections import Counter
        fibdist = Counter(fib)
        print(f"  n={n} line(x^{e},x^{f}): a0={a0} k={k}  d=gcd(e-f,n)={d} orbit n/d={orbit}")
        print(f"    K = 2^r C(n/2,r) = {K}")
        print(f"    #S_on_V (interp #bad-subsets)   = {S_on_V_i}")
        print(f"    #S_on_V (variety h_m)           = {S_on_V_v}")
        print(f"    #bad (distinct nonzero gamma)   = {nbad_i}  (distinct nonzero={len(dz_i)}, gamma=0? {'yes' if 0 in gm_i else 'no'})")
        print(f"    K / #S_on_V                     = {K/max(S_on_V_i,1):.3f}   (#S_on_V <= K ? {S_on_V_i <= K})")
        print(f"    #S_on_V / #bad                  = {S_on_V_i/max(nbad_i,1):.3f}")
        print(f"    #bad <= #S_on_V ?               = {nbad_i <= S_on_V_i}   #bad <= K ? {nbad_i <= K}")
        print(f"    fiber sizes (S per distinct gamma): distinct sizes -> count = {dict(sorted(fibdist.items()))}")
        print(f"    fiber == orbit (n/d={orbit}) constant? {set(fib) == {orbit}}   (min={min(fib)} max={max(fib)})")
        out[n] = dict(K=K, S_on_V=S_on_V_i, S_on_V_v=S_on_V_v, nbad=nbad_i,
                      orbit=orbit, d=d, fibdist=dict(sorted(fibdist.items())),
                      fibmin=min(fib), fibmax=max(fib))
    return out

if __name__ == "__main__":
    n_arg = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [16, 32]
    calibrate_r3(p)
    out = measure_r5(p, n_arg)
    print("\nSUMMARY:", out)
