#!/usr/bin/env python3
"""G100F probe: smallDiffPairs(b*mu_n, W) counting across the window sweep.

Objects (G80Q terminal form):
  C = b*mu_n subset ZMod p,  sdp(b, W) = #{(u,z) in C^2 : u != z, u-z in Strip(W)}
  Strip(W) = {w : val(w) <= W or val(w) >= p-W}   (signed window |lift| <= W)

Questions:
 (1) where does sdp leave 0?  (vs p/(2n^2) birthday and sqrt(p/2) G99 scale)
 (2) growth vs uniform line n(n-1)*(2W)/(p-1)  across  1 -> p/4, esp. [sqrt(p), p/K]
 (3) verify the new coset-product-trick bound sdp <= n * (314880 W^2 n^4)^(1/8)
     (per-ratio N_d^8 <= 314880 W^2 n^4, sdp = sum_d N_d)
 (4) per-ratio distribution max N_d vs mean (cost of the (n-1)*max step)
 (5) multiplicative structure of lifted differences (Omega, gcds, ratio-in-H check)
"""
import math, random, sys
from bisect import bisect_right

random.seed(2026)

def is_prime(x):
    if x < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if x % q == 0: return x == q
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        v = pow(a, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True

def find_prime(n, beta):
    """smallest prime p = 1 mod n with p >= n^beta"""
    target = int(round(n**beta))
    p = target - (target % n) + 1
    while not is_prime(p): p += n
    return p

def primitive_root(p):
    fac = []
    m = p-1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g

def subgroup(p, n):
    g = primitive_root(p)
    x = pow(g, (p-1)//n, p)
    H = []
    v = 1
    for _ in range(n):
        H.append(v); v = v*x % p
    assert v == 1 and len(set(H)) == n
    return H, g

def circdists(C, p):
    """sorted list of circular distances (1..p/2) over unordered pairs"""
    ds = []
    m = len(C)
    Cs = sorted(C)
    for i in range(m):
        for j in range(i+1, m):
            d = Cs[j] - Cs[i]
            ds.append(min(d, p-d))
    ds.sort()
    return ds

def sdp_from_dists(ds, W):
    # ordered pairs = 2 * unordered with dist in [1, W]  (dist >= 1 always, u != z)
    return 2 * bisect_right(ds, W)

def omega_big(x):
    c = 0; d = 2
    while d*d <= x:
        while x % d == 0: c += 1; x //= d
        d += 1
    if x > 1: c += 1
    return c

def signed_lift(w, p):
    return w if 2*w <= p else w - p

def main():
    cells = [(16, 3.0), (16, 4.0), (32, 2.5), (32, 3.0), (32, 4.0),
             (64, 2.5), (64, 3.0), (128, 2.25), (256, 2.0)]
    for n, beta in cells:
        p = find_prime(n, beta)
        H, g = subgroup(p, n)
        K_saddle = max(2, round(math.sqrt(2*math.pi*n/math.log(p))))
        W_prize = p // K_saddle
        sqp = math.isqrt(p//2)
        n_cosets = (p-1)//n
        # sample cosets: all if <= 400 else random 400 (always include b=1's coset rep set)
        if n_cosets <= 400:
            reps = [pow(g, j, p) for j in range(n_cosets)]
        else:
            reps = [pow(g, j, p) for j in random.sample(range(n_cosets), 400)]
        print(f"\n=== n={n} beta={beta} p={p} (p~n^{math.log(p)/math.log(n):.2f}) "
              f"K_saddle={K_saddle} W_prize={W_prize} sqrt(p/2)={sqp} "
              f"cosets={n_cosets} sampled={len(reps)}")
        # W grid: log-spaced 1..p//4 plus the landmarks
        Wgrid = sorted(set([int(round((p/4)**(k/28))) for k in range(1, 29)]
                           + [sqp, W_prize, p//(2*n*n) if p//(2*n*n)>0 else 1]))
        Wgrid = [W for W in Wgrid if W >= 1]
        # per-coset distance lists
        allds = {}
        first_nonzero = []
        for b in reps:
            C = [b*h % p for h in H]
            ds = circdists(C, p)
            allds[b] = ds
            first_nonzero.append(ds[0])
        w0_min = min(first_nonzero); w0_med = sorted(first_nonzero)[len(first_nonzero)//2]
        print(f"  first small-diff (min gap): min over cosets={w0_min}, median={w0_med}, "
              f"birthday p/(2n^2)={p/(2*n*n):.1f}")
        print(f"  {'W':>10} {'sdp_max':>10} {'sdp_mean':>10} {'uniform':>12} "
              f"{'max/unif':>9} {'newbnd':>12} {'max/newbnd':>10} {'mark':>8}")
        for W in Wgrid:
            vals = [sdp_from_dists(allds[b], W) for b in reps]
            mx = max(vals); mean = sum(vals)/len(vals)
            unif = n*(n-1)*(2*W)/(p-1)
            newbnd = n * (314880 * W*W * n**4)**(1/8)   # sdp <= n * (314880 W^2 n^4)^{1/8}
            mark = ""
            if W == sqp: mark = "<-sqrt(p/2)"
            if W == W_prize: mark = "<-PRIZE W"
            in_win = "*" if 2*W*W < p else " "
            print(f"  {W:>10} {mx:>10} {mean:>10.1f} {unif:>12.2f} "
                  f"{(mx/unif if unif>0 else float('inf')):>9.2f} {newbnd:>12.0f} "
                  f"{mx/newbnd:>10.3f}{in_win} {mark:>10}")
        # per-ratio structure at W ~ sqrt(p/2) (worst coset)
        Wstr = sqp
        worst_b, worst_v = None, -1
        for b in reps:
            v = sdp_from_dists(allds[b], Wstr)
            if v > worst_v: worst_v, worst_b = v, b
        b = worst_b
        C = [b*h % p for h in H]
        Hset = set(H)
        # per-ratio N_d and lifted-diff structure
        Nd = {}
        lifts = []
        for hi in H:
            for hj in H:
                if hi == hj: continue
                u, z = b*hi % p, b*hj % p
                w = (u - z) % p
                lift = signed_lift(w, p)
                if abs(lift) <= Wstr:
                    d = hi * pow(hj, p-2, p) % p
                    Nd[d] = Nd.get(d, 0) + 1
                    lifts.append((lift, d, z))
        if Nd:
            ndv = sorted(Nd.values())
            print(f"  per-ratio @W=sqrt(p/2), worst coset b={b}: sdp={worst_v}, "
                  f"#active ratios={len(Nd)}/{n-1}, N_d max={ndv[-1]} mean={sum(ndv)/len(ndv):.2f}")
            # ratio-in-H check: same-d lifts m, m' should satisfy m/m' in H (mod p)
            byd = {}
            for lift, d, z in lifts: byd.setdefault(d, []).append(lift)
            ok, tot = 0, 0
            for d, ms in byd.items():
                for i in range(len(ms)):
                    for j in range(i+1, len(ms)):
                        tot += 1
                        r = ms[i] % p * pow(ms[j] % p, p-2, p) % p
                        if r in Hset: ok += 1
            print(f"  same-ratio lift pairs with m/m' in H (mod p): {ok}/{tot}")
            # integer structure
            oms = [omega_big(abs(m)) for m, _, _ in lifts]
            print(f"  Omega(|lift|): mean={sum(oms)/len(oms):.2f} max={max(oms)} "
                  f"(log2 W ~ {math.log2(Wstr):.1f}); distinct |lifts|={len(set(abs(m) for m,_,_ in lifts))}"
                  f"/{len(lifts)}")
            gs = []
            sample = [abs(m) for m, _, _ in lifts][:200]
            for i in range(len(sample)):
                for j in range(i+1, len(sample)):
                    gs.append(math.gcd(sample[i], sample[j]))
            if gs:
                frac_g1 = sum(1 for x in gs if x == 1)/len(gs)
                print(f"  pairwise gcd of |lifts|: frac coprime={frac_g1:.2f}, "
                      f"max gcd={max(gs)}")
        sys.stdout.flush()

if __name__ == "__main__":
    main()
