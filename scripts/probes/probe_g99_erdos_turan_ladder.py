#!/usr/bin/env python3
"""G99 probe: Erdos-Turan / Esseen ladder with the EXACT in-tree second moment.

Chain under test (worst-b, fully unconditional inputs only):
  (ET)      D*(b) <= n/(H+1) + 3 * sum_{h<=H} |eta_{hb}|/h
  (CS+orbit) sum_{h<=H} |eta_{hb}|/h <= sqrt(sum 1/h^2) * sqrt(sum_{h<=H}|eta_{hb}|^2)
  (coset-Parseval, if ladder hits distinct mu_n-cosets)
            sum_{h<=H} |eta_{hb}|^2 <= (p*n - n^2)/n = p - n     [b-uniform!]
  => D*(b) <= n/(H+1) + 3*sqrt(2)*sqrt(p-n)   (elementary partial-zeta bound sqrt2)
     (sharp constant pi/sqrt6 = 1.2825 instead of sqrt2 = 1.4142)

Also: cross-Parseval completion bound per arc:
  |p*occ(I) - n*|I|| <= sqrt(|I|(p-|I|)) * sqrt(n(p-n))
Loop via G80Z consumer: M <= 2*pi*n/K + 2*K*D*  -- AM-GM floor 2*sqrt(2*pi*n*Delta).
Small-ball rigidity (Part 2): no dilate b*mu_n inside any circular interval of
  length V when 2V^2 < p (integer-lift multiplicativity argument).
"""
import numpy as np, math

def eta_all(p, pts):
    ind = np.zeros(p, dtype=complex)
    for x in pts: ind[x] += 1.0
    # eta_b = sum_x e_p(bx) = conj-DFT; |eta| symmetric anyway
    return np.fft.fft(ind)   # F[b] = sum_x ind[x] e^{-2pi i bx/p}; |F[b]|=|eta_b|

def mu_subgroup(p, n):
    # elements of order dividing n: g^((p-1)/n * k)
    g = primitive_root(p)
    step = pow(g, (p-1)//n, p)
    pts, cur = [], 1
    for _ in range(n):
        pts.append(cur); cur = cur*step % p
    assert len(set(pts)) == n
    return pts

def primitive_root(p):
    fac = factor(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    raise ValueError

def factor(m):
    f, d = set(), 2
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f

def star_disc_counts(vals, p, n):
    """D* in COUNT units: sup_t |#{x < t} - n t/p| over t in [0,p]."""
    s = np.sort(np.array(vals))
    # candidates at jump points
    i = np.arange(1, n+1)
    d1 = np.max(np.abs(i - n*(s+1)/p))
    d0 = np.max(np.abs((i-1) - n*s/p))
    return max(d1, d0)

def ladder(absF, p, b, H):
    return sum(absF[(h*b) % p]/h for h in range(1, H+1))

def coset_free_H(p, n, pts):
    mu = set(pts); inv = {x: pow(x, p-2, p) for x in range(1, 4000)}
    H = 1
    while H < 3000:
        Hn = H+1
        ok = all((hp * pow(h, p-2, p)) % p not in mu
                 for h in range(1, Hn) for hp in [Hn])
        if not ok: break
        H = Hn
    return H

def cell(p, n, K=16, Hlist=(8, 32, 128)):
    pts = mu_subgroup(p, n)
    F = eta_all(p, pts); absF = np.abs(F)
    absF[0] = 0
    M = absF.max(); bstar = int(absF.argmax())
    target = math.sqrt(n*math.log(p/n))
    Ds = star_disc_counts([(bstar*x) % p for x in pts], p, n)
    cert = math.sqrt(2)*math.sqrt(p-n)           # formalized constant
    cert_sharp = (math.pi/math.sqrt(6))*math.sqrt(p-n)
    H0 = coset_free_H(p, n, pts)
    print(f"\n=== cell p={p} n={n} (beta={math.log(p)/math.log(n):.2f}, "
          f"n/sqrt(p)={n/math.sqrt(p):.2f}) ===")
    print(f"  M={M:.1f}  M/sqrt(n log(p/n))={M/target:.3f}  b*={bstar}")
    print(f"  worst-b star-discrepancy D*(b*)={Ds:.1f}  (trivial cap n={n})")
    print(f"  coset-collision-free ladder depth H0={H0}  sqrt(p/n)={math.sqrt(p/n):.1f}")
    for H in Hlist:
        L = ladder(absF, p, bstar, H)
        l2 = sum(absF[(h*bstar) % p]**2 for h in range(1, H+1))
        et = n/(H+1) + 3*L
        et_cert = n/(H+1) + 3*cert
        print(f"  H={H:4d}: ladder={L:9.1f} CS-coset-cert={cert:9.1f} "
              f"(sharp {cert_sharp:8.1f})  l2={l2:12.1f} vs p-n={p-n} "
              f"ETtruth={et:9.1f} ETcert={et_cert:9.1f} "
              f"[{'NONTRIV' if et_cert < n else 'vacuous'} vs n]")
    # per-arc cross-Parseval check (K arcs)
    Larc = p//K
    occ = np.zeros(K, dtype=int)
    for x in pts: occ[min((K*((bstar*x) % p))//p, K-1)] += 1
    devmax = np.max(np.abs(occ - n/K))
    cp = math.sqrt(Larc*(p-Larc))*math.sqrt(n*(p-n))/p
    print(f"  K={K} arcs, worst-b: max|occ-n/K|={devmax:.1f}, cross-Parseval "
          f"cert={cp:.1f}, trivial n/K={n/K:.1f} -> {'NONTRIV' if cp < n/K else 'vacuous'}")
    # loop floor
    Delta = cert  # per-arc deviation certificate scale
    floor = 2*math.sqrt(2*math.pi*n*Delta)
    print(f"  G80Z-loop AM-GM floor 2 sqrt(2 pi n Delta) = {floor:.1f}  "
          f"vs M={M:.1f} vs sqrt(p)={math.sqrt(p):.1f} vs n={n} "
          f"[loop {'contracts' if floor < M else 'DOES NOT contract'}]")

def rigidity(p, n):
    """Part 2 check: min over b of the shortest circular interval containing b*mu_n."""
    pts = mu_subgroup(p, n)
    best = (p, None)
    for b in range(1, p):
        v = sorted((b*x) % p for x in pts)
        gaps = [(v[(i+1) % n] - v[i]) % p for i in range(n)]
        cover = p - max(gaps) + 1
        if cover < best[0]: best = (cover, b)
    thr = math.sqrt(p/2)
    print(f"  p={p} n={n}: min over b of covering-interval length = {best[0]} "
          f"(b={best[1]}), theorem threshold V<sqrt(p/2)={thr:.1f} "
          f"-> {'CONSISTENT' if best[0] > thr else 'VIOLATION!'}")

print("#### thin / prize-shape cells ####")
cell(65537, 16)          # beta = 4 exactly
cell(65537, 32)
print("\n#### mid & dense cells (where is the certificate nontrivial?) ####")
cell(65537, 256)         # n = sqrt(p)
cell(65537, 4096, Hlist=(8, 32, 128, 1024))   # n = 16 sqrt(p)
cell(257, 64, K=8, Hlist=(4, 8, 16))          # n = 4 sqrt(p)
cell(257, 128, K=8, Hlist=(4, 8, 16))         # n = 8 sqrt(p)
print("\n#### Part-2 small-ball rigidity (exhaustive) ####")
rigidity(1553, 16)
rigidity(257, 16)
rigidity(257, 64)
rigidity(97, 32)
