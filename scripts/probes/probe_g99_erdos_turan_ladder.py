#!/usr/bin/env python3
"""G99 probe: Erdos-Turan / Esseen ladder with the EXACT in-tree second moment.

Chain under test (worst-b, fully unconditional inputs only):
  (ET)      D*(b) <= n/(H+1) + 3 * sum_{h<=H} |eta_{hb}|/h
  (CS+orbit) sum_{h<=H} |eta_{hb}|/h <= sqrt(sum 1/h^2) * sqrt(sum_{h<=H}|eta_{hb}|^2)
  (coset-Parseval, if ladder hits distinct mu_n-cosets)
            sum_{h<=H} |eta_{hb}|^2 <= (p*n - n^2)/n = p - n     [b-uniform!]
  => D*(b) <= n/(H+1) + 3*sqrt(2)*sqrt(p-n)   (elementary partial-zeta bound sqrt2)
     (sharp constant pi/sqrt6 = 1.2825 instead of sqrt2 = 1.4142)
  This sqrt(2)*sqrt(p-n) certificate is printed ONLY for H <= H0, the coset-collision-free
  depth.  Beyond H0 the ladder repeats mu_n-cosets and the bound can be false (e.g. p=257,
  n=128, H=8: index 2, both periods (-1 +- sqrt 257)/2 exceed 15/2 in absolute value, so the
  ladder exceeds (15/2)*(761/280) > 20 > sqrt(258)).  For every H the script also prints the
  valid multiplicity-weighted certificate: |eta_{hb}| is constant on h*mu_n, so grouping
  h <= H by coset C with weight w_C = sum_{h in C, h<=H} 1/h and using
  sum_C |eta_C|^2 = p - n gives  ladder <= sqrt(sum_C w_C^2) * sqrt(p-n).

Also: cross-Parseval completion bound per arc:
  |p*occ(I) - n*|I|| <= sqrt(|I|(p-|I|)) * sqrt(n(p-n))
  (checked per arc with the exact integer arc lengths |I_j| and centering n*|I_j|/p).
Loop via G80Z consumer: M <= 2*pi*n/K + 2*K*Delta -- continuous AM-GM minimum over K
  is 4*sqrt(pi*n*Delta) (at K = sqrt(pi*n/Delta)); Delta here is the collision-free ladder
  certificate scale sqrt(2)*sqrt(p-n), used as a heuristic scale, not a proved D* bound.
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
    """D* in COUNT units: sup_t |#{x < t} - n t/p| over real t in [0,p].

    For sorted points s_1 < ... < s_n the count is i on (s_i, s_{i+1}], so the supremum is
    attained at t = s_i (count i-1) or approached as t -> s_i from the right (count i).
    (The former version used s_i + 1 for the right side, i.e. integer t only; on {1} mod 5
    it returned 0.6 instead of the continuous supremum 0.8.)"""
    s = np.sort(np.array(vals, dtype=float))
    # candidates at jump points
    i = np.arange(1, n+1)
    d1 = np.max(np.abs(i - n*s/p))
    d0 = np.max(np.abs((i-1) - n*s/p))
    return max(d1, d0)

def ladder(absF, p, b, H):
    return sum(absF[(h*b) % p]/h for h in range(1, H+1))

def coset_weight_sq(p, n, H):
    """sum over mu_n-cosets C of (sum_{h in C, 1<=h<=H} 1/h)^2  (requires H < p).

    h, h' lie in the same coset h*mu_n iff h^n = h'^n mod p.  Equals sum_{h<=H} 1/h^2 when
    the ladder is coset-collision-free (H <= H0)."""
    assert H < p, "ladder index h = p would hit eta_0"
    w = {}
    for h in range(1, H+1):
        key = pow(h, n, p)
        w[key] = w.get(key, 0.0) + 1.0/h
    return sum(x*x for x in w.values())

def weighted_coset_cert(p, n, H):
    """Valid for every H < p: sum_{h<=H}|eta_{hb}|/h <= sqrt(sum_C w_C^2) * sqrt(p-n)."""
    return math.sqrt(coset_weight_sq(p, n, H))*math.sqrt(p-n)

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
        wcert = weighted_coset_cert(p, n, H)   # valid at every H < p
        et_cert = n/(H+1) + 3*wcert
        if H <= H0:
            cs = (f"CS-coset-cert={cert:9.1f} (sharp {cert_sharp:8.1f})")
        else:
            cs = (f"CS-coset-cert=   n/a (H>H0={H0}: ladder repeats cosets)")
        print(f"  H={H:4d}: ladder={L:9.1f} {cs}  weighted-coset-cert={wcert:9.1f}  "
              f"l2={l2:12.1f} "
              f"ETtruth={et:9.1f} ETcert(weighted)={et_cert:9.1f} "
              f"[{'NONTRIV' if et_cert < n else 'vacuous'} vs n]")
        # numerical sanity (FFT roundoff tolerance): the certificate must contain the truth
        assert L <= wcert*(1 + 1e-9) + 1e-9, (p, n, H, L, wcert)
    # per-arc cross-Parseval check (K arcs I_j = [j p/K, (j+1) p/K) with exact integer
    # lengths |I_j| and centering n*|I_j|/p)
    lens = np.array([-((-(j+1)*p)//K) + ((-j*p)//K) for j in range(K)])   # ceil diffs
    assert lens.sum() == p
    occ = np.zeros(K, dtype=int)
    for x in pts: occ[(K*((bstar*x) % p))//p] += 1
    dev = np.abs(occ - n*lens/p)
    cps = np.sqrt(lens*(p-lens))*math.sqrt(n*(p-n))/p
    assert np.all(dev <= cps*(1 + 1e-12)), "cross-Parseval per-arc bound violated"
    cp = float(cps.max())
    triv = float((n*lens/p).min())
    print(f"  K={K} arcs (|I_j| in {sorted(set(lens.tolist()))}), worst-b: "
          f"max_j|occ_j-n|I_j|/p|={dev.max():.1f}, max_j cross-Parseval cert={cp:.1f} "
          f"(holds on every arc), min_j n|I_j|/p={triv:.1f} -> "
          f"{'NONTRIV' if cp < triv else 'vacuous'}")
    # loop floor
    Delta = cert  # collision-free ladder certificate scale (heuristic, see header)
    floor = 4*math.sqrt(math.pi*n*Delta)
    print(f"  G80Z-loop AM-GM floor 4 sqrt(pi n Delta) = {floor:.1f}  "
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

def main():
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

if __name__ == "__main__":
    main()
