#!/usr/bin/env python3
"""G90 probe: spacing rigidity / Denjoy-Koksma angle for arc occupancy of b*mu_n in ZMod p.

For toy primes p, n | p-1, n ~ sqrt(p) (n = 2^a, smooth, prize shape):
  1. exact star discrepancy (count units) of b*mu_n for ALL dilation cosets b;
  2. compare against sqrt(n log p) (target scale) and random baseline;
  3. interval-exchange test: does mult-by-g act on SORTED values of b*mu_n with
     a bounded number of adjacency-preserving branches? (rotation orbits: 3)
  4. gap-count statistics (cross-check E12);
  5. Cilleruelo-Garaev room: max over b, arcs of |arc cap b*mu_n| for K arcs.
"""
import math, random, sys

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def find_primes(n, lo, hi, count=3):
    """primes p = 1 mod n in [lo, hi]"""
    out = []
    p = lo - (lo - 1) % n  # p = 1 mod n
    if p < lo: p += n
    while p <= hi and len(out) < count:
        if is_prime(p): out.append(p)
        p += n
    return out

def subgroup(p, n):
    """mu_n in ZMod p, and a generator g of mu_n."""
    # find generator of full group then power up
    def order(a):
        # order divides p-1
        o = p-1
        f = factorize(p-1)
        for q in f:
            while o % q == 0 and pow(a, o//q, p) == 1:
                o //= q
        return o
    a = 2
    while True:
        g = pow(a, (p-1)//n, p)
        if order(g) == n:
            break
        a += 1
    S = []
    x = 1
    for _ in range(n):
        S.append(x); x = x*g % p
    assert x == 1
    assert len(set(S)) == n
    return S, g

def factorize(m):
    f = set(); d = 2
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f

def star_discrepancy_count(vals, p):
    """exact sup over intervals [0,t) t in (0,p] of |#{v < t} - n*t/p|, count units.
    With sorted v_0<...<v_{n-1}: sup = max_i max(| (i+1) - n*(v_i+1)/p |? ) --
    use standard: D* = max_i max( (i+1)/n - v_i/p , v_i/p - i/n ) * n  (points at v_i/p)."""
    v = sorted(vals); n = len(v)
    best = 0.0
    for i, x in enumerate(v):
        t = x / p
        best = max(best, abs((i+1) - n*t), abs(i - n*t))
    return best

def two_sided_disc(vals, p, K):
    """max over the K canonical arcs [jp/K,(j+1)p/K) of |occ - n/K|."""
    n = len(vals); cnt = [0]*K
    for x in vals: cnt[K*x//p] += 1
    m = n/K
    return max(abs(c - m) for c in cnt), max(cnt), min(cnt)

def branch_count(vals, g, p):
    """S sorted v_0<..<v_{n-1}; pi(i) = rank of g*v_i. Count maximal runs with
    pi(i+1) = pi(i)+1 (linear adjacency); also cyclic version mod n."""
    v = sorted(vals); n = len(v)
    rank = {x: i for i, x in enumerate(v)}
    pi = [rank[(g*x) % p] for x in v]
    runs = 1
    for i in range(n-1):
        if pi[i+1] != pi[i] + 1:
            runs += 1
    cyc_runs = sum(1 for i in range(n) if pi[(i+1) % n] != (pi[i]+1) % n)
    return runs, cyc_runs

def gap_count(vals, p):
    v = sorted(vals); n = len(v)
    gaps = set()
    for i in range(n):
        gaps.add((v[(i+1) % n] - v[i]) % p)
    return len(gaps)

def eta_norm(vals, p):
    s = sum(complex(math.cos(2*math.pi*x/p), math.sin(2*math.pi*x/p)) for x in vals)
    return abs(s)

def run_cell(p, n, seed=0):
    S, g = subgroup(p, n)
    cosets = (p-1)//n
    # coset representatives: powers of a full-group generator
    # simpler: iterate b over 1..p-1, mark cosets
    seen = set(); reps = []
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        for x in S: seen.add(b*x % p)
        if len(reps) == cosets: break
    target = math.sqrt(n*math.log(p))
    target2 = math.sqrt(n*math.log(p/n))
    Dmax, Dmax_b = 0, None
    branch_max, branch_min = 0, 10**9
    cycb_max = 0
    gmax = 0
    etamax = 0.0
    Ds = []
    for b in reps:
        T = [b*x % p for x in S]
        D = star_discrepancy_count(T, p)
        Ds.append(D)
        if D > Dmax: Dmax, Dmax_b = D, b
        r, cr = branch_count(T, g, p)
        branch_max = max(branch_max, r); branch_min = min(branch_min, r)
        cycb_max = max(cycb_max, cr)
        gmax = max(gmax, gap_count(T, p))
        etamax = max(etamax, eta_norm(T, p))
    Ds.sort()
    med = Ds[len(Ds)//2]
    # random baseline: same n, uniform without replacement, over #cosets trials
    rng = random.Random(seed)
    RDs = []
    for _ in range(min(cosets, 64)):
        T = rng.sample(range(p), n)
        RDs.append(star_discrepancy_count(T, p))
    RDs.sort()
    rmax, rmed = RDs[-1], RDs[len(RDs)//2]
    print(f"p={p} n={n} beta=log_n(p)={math.log(p)/math.log(n):.3f} cosets={cosets}")
    print(f"  sqrt(n log p)={target:.2f} sqrt(n log(p/n))={target2:.2f}")
    print(f"  D*max={Dmax:.2f} (b={Dmax_b}) med={med:.2f}  C=Dmax/sqrt(n log p)={Dmax/target:.3f}"
          f"  C2=Dmax/sqrt(n log(p/n))={Dmax/target2:.3f}")
    print(f"  random baseline ({len(RDs)} trials n pts): max={rmax:.2f} med={rmed:.2f}"
          f"  Crand=max/sqrt(n log p)={rmax/target:.3f}")
    print(f"  eta_max={etamax:.2f}  eta/sqrt(n log(p/n))={etamax/target2:.3f}")
    print(f"  branches(sorted mult-by-g): min={branch_min} max={branch_max}"
          f" cyclic_max={cycb_max}  (rotation would be <=3; n/2+1={n//2+1})")
    print(f"  max #distinct gaps={gmax} (E12 ceiling n/2+1={n//2+1})")
    # K-arc occupancy at prize K ~ n/sqrt(n log(p/n))
    K = max(2, round(n/target2))
    occmax, cmax, cmin = 0, 0, 10**9
    for b in reps:
        T = [b*x % p for x in S]
        d, cM, cm = two_sided_disc(T, p, K)
        occmax = max(occmax, d); cmax = max(cmax, cM); cmin = min(cmin, cm)
    print(f"  K={K} arcs (prize shape): max|occ - n/K|={occmax:.2f} n/K={n/K:.2f}"
          f" occ range=[{cmin},{cmax}]  needed eps for K*eps<=sqrt(n log q): {target2/K:.2f}")
    print()
    return dict(p=p, n=n, Dmax=Dmax, C=Dmax/target, branch_min=branch_min,
                branch_max=branch_max)

def main():
    cells = []
    for n in (16, 32, 64, 128, 256):
        lo, hi = n*n//2, 3*n*n
        ps = find_primes(n, lo, hi, count=2)
        for p in ps: cells.append((p, n))
    # the beautiful Fermat cell
    if (65537, 256) not in cells: cells.append((65537, 256))
    # one thicker cell n ~ p^{1/3} for contrast
    ps = find_primes(64, 64**3//2, 64**3*2, count=1)
    for p in ps: cells.append((p, 64))
    for p, n in cells:
        run_cell(p, n)

if __name__ == "__main__":
    main()
