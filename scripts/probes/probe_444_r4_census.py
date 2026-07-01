# #444 demand-side r=4 census probe (optimized).
# PROVEN clean reduction (Schur-ratio identity in complete-homogeneous h_m):
#   S (r+1-subset of mu_n) BAD for line (x^e,x^f) <=>
#     h_{e-r}(S)*h_{f-r+1}(S) = h_{f-r}(S)*h_{e-r+1}(S)   [variety V]
#   pinned bad scalar gamma = - h_{e-r}(S)/h_{f-r}(S).
# h_m(S) via elementary symmetric e_k(S) and the relation
#   h_m = sum over compositions; easier: build generating fn 1/prod(1-z t) = sum h_m t^m.
# We compute h_0..h_mmax directly from the multiset by polynomial multiplication of
# the series 1/(1-z t) truncated to degree mmax, which is O(a*mmax) per subset.
#
# CALIBRATION (anti-fabrication): r=3 in-tree DeepBandR3Bound:
#   #bad = n*C(n/4,2)+1 ; O_P(3)=C(n/4,2) = 6,28 at n=16,32.
from math import comb, gcd
from itertools import combinations
from collections import Counter

P1 = 2013265921          # BabyBear, 2^27 | p-1
P2 = 3221225473          # cross-check prime, 2^30 | p-1

def mu_n(n, p):
    assert (p-1) % n == 0
    e = (p-1)//n
    for c in range(2, 500):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and pow(h, n//2, p) != 1:
            return [pow(h, i, p) for i in range(n)]
    raise RuntimeError("no generator")

def h_series_from_elts(elts, mmax, p):
    # series H(t) = prod_z 1/(1-z t) mod t^{mmax+1}.
    # multiply in factor 1/(1-z t) = sum_{k} z^k t^k truncated.
    H = [0]*(mmax+1); H[0] = 1
    for z in elts:
        # H *= 1/(1-z t):  new[m] = sum_{k=0}^m H_old[k]*z^{m-k}
        # equivalently recurrence: newH[m] = H[m] + z*newH[m-1]
        for m in range(1, mmax+1):
            H[m] = (H[m] + z*H[m-1]) % p
    return H

def census(n, p, r, e, f):
    a = r+1
    ie, ie1, jf, jf1 = e-r, e-r+1, f-r, f-r+1
    idxs = [ie, ie1, jf, jf1]
    assert min(idxs) >= 0, f"negative h index: {idxs}"
    mmax = max(idxs)
    dom = mu_n(n, p)
    S_on_V = 0
    fiber = {}        # gamma -> count of S
    gamma_zero = 0
    inf_ct = 0
    invcache = {}
    for S in combinations(range(n), a):
        elts = [dom[i] for i in S]
        H = h_series_from_elts(elts, mmax, p)
        he, he1, hf, hf1 = H[ie], H[ie1], H[jf], H[jf1]
        if (he*hf1 - hf*he1) % p == 0:
            S_on_V += 1
            if hf % p == 0:
                inf_ct += 1
            else:
                inv = invcache.get(hf)
                if inv is None:
                    inv = pow(hf, p-2, p); invcache[hf] = inv
                g = (-he * inv) % p
                if g == 0:
                    gamma_zero += 1
                fiber[g] = fiber.get(g, 0) + 1
    return S_on_V, fiber, gamma_zero, inf_ct

def distinct_nonzero_gamma(fiber):
    return sum(1 for g in fiber if g != 0)

def report_line(n, p, r, e, f, label):
    S_on_V, fiber, gz, inf_ct = census(n, p, r, e, f)
    K = (1 << r) * comb(n//2, r)
    nd = distinct_nonzero_gamma(fiber)
    has_zero = 1 if gz > 0 else 0
    bad = nd + has_zero
    d = gcd(abs(e-f), n); orbit = n//d
    nz_sizes = sorted(cnt for g, cnt in fiber.items() if g != 0)
    print(f"  n={n:3d} p={p} line=(x^{e},x^{f}) [{label}]")
    print(f"    #S_on_V={S_on_V}  #bad(distinct gamma)={bad}  K={K}")
    print(f"    S_on_V<=K? {S_on_V<=K}   bad<=S_on_V? {bad<=S_on_V}   bad<=K? {bad<=K}")
    if S_on_V:
        print(f"    ratios: S_on_V/K={S_on_V/K:.4f}  bad/K={bad/K:.4f}  bad/S_on_V={bad/S_on_V:.4f}")
    print(f"    gamma_zero_present={has_zero}  #distinct_nonzero_gamma={nd}  inf_pins(hf=0)={inf_ct}")
    print(f"    dilation d=gcd(e-f,n)={d} -> predicted orbit size n/d={orbit}  O_P={nd//orbit if orbit else 0}")
    if nz_sizes:
        sz = Counter(nz_sizes)
        print(f"    fiber-size distribution (size->#gammas): {dict(sorted(sz.items()))}")
        print(f"    fiber sizes: min={min(nz_sizes)} max={max(nz_sizes)} all==n/d? {all(s==orbit for s in nz_sizes)}")
    return dict(S_on_V=S_on_V, bad=bad, K=K, nd=nd, orbit=orbit, gz=gz, inf_ct=inf_ct,
                fiber_sizes=nz_sizes)

def find_r3_calibration(n, p):
    # r=3 maximizer: scan lines, report the one matching target #bad = n*C(n/4,2)+1.
    r = 3
    target_bad = n*comb(n//4, 2) + 1
    target_OP = comb(n//4, 2)
    best = None
    for e in range(r, n):
        for f in range(r, n):
            if e == f: continue
            if min(e-r, e-r+1, f-r, f-r+1) < 0: continue
            S_on_V, fiber, gz, inf_ct = census(n, p, r, e, f)
            nd = distinct_nonzero_gamma(fiber)
            bad = nd + (1 if gz>0 else 0)
            if bad == target_bad:
                d = gcd(abs(e-f), n); orbit = n//d
                OP = nd//orbit if orbit else 0
                best = (e, f, bad, S_on_V, OP, orbit)
                break
        if best: break
    return best, target_bad, target_OP

if __name__ == "__main__":
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else "calib"

    if mode == "calib":
        print("="*70)
        print("CALIBRATION r=3 (target: #bad=n*C(n/4,2)+1, O_P=C(n/4,2)=6,28)")
        print("="*70)
        for n in [16, 32]:
            best, tb, tOP = find_r3_calibration(n, P1)
            if best:
                e,f,bad,S_on_V,OP,orbit = best
                print(f"  n={n}: line (x^{e},x^{f}) #bad={bad}==target{tb}? {bad==tb}  "
                      f"O_P={OP}==target{tOP}? {OP==tOP}  orbit={orbit}  S_on_V={S_on_V}")
            else:
                print(f"  n={n}: CALIBRATION FAILED (no line hit target {tb})")

    if mode in ("calib", "r4_16"):
        print("="*70); print("r=4 MAXIMIZER (x^{n/2+2},x^{n/4+1}) n=16  -- expect O_P=9"); print("="*70)
        n=16; e=n//2+2; f=n//4+1
        report_line(n, P1, 4, e, f, "maximizer")
        report_line(n, P2, 4, e, f, "cross-check P2")

    if mode in ("calib", "r4_32"):
        print("="*70); print("r=4 MAXIMIZER n=32  -- expect O_P=97"); print("="*70)
        n=32; e=n//2+2; f=n//4+1
        report_line(n, P1, 4, e, f, "maximizer")

    if mode == "r4_64":
        print("="*70); print("r=4 MAXIMIZER n=64  -- expect O_P=897"); print("="*70)
        n=64; e=n//2+2; f=n//4+1
        report_line(n, P1, 4, e, f, "maximizer")

    print("Done.")
