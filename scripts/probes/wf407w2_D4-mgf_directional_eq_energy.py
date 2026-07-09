# -*- coding: utf-8 -*-
"""
wf407-w2 / D4-mgf : confirm the COLLAPSE -- the per-period DIRECTIONAL even moments equal the
ABSOLUTE energy moments, so the per-period MGF carries the deep-moment energy wall and is NOT a
distinct decomposition. We show the AVERAGE over direction is an EXACT identity, and the WORST
direction (the one the MGF/Chernoff actually uses) does NOT escape it.

Setup. For unit zeta, X_c(zeta) = Re(conj(zeta) eta_c).
  AVERAGE-over-direction even moment (zeta uniform on the circle):
     (1/2pi) int X_c(zeta)^{2r} dzeta = binom(2r,r)/4^r * |eta_c|^{2r}.
  So  (1/m) sum_c E_zeta[X_c^{2r}] = (binom(2r,r)/4^r) * (1/m) sum_c |eta_c|^{2r}
                                   = (binom(2r,r)/4^r) * E_r(mu_n).
  i.e. the DIRECTION-AVERAGED directional 2r-moment is the additive energy E_r times an explicit
  combinatorial constant. The directional MGF therefore cannot avoid E_r: its moments ARE the
  energy (up to a fixed constant), so bounding the MGF == bounding E_r to r ~ log m == the wall.

We verify:
  (V1) the identity (1/m) sum_c avg_zeta X_c^{2r} = (binom(2r,r)/4^r) E_r   EXACTLY (to 1e-9).
  (V2) the WORST-direction 2r-moment is >= the direction-AVERAGE (so the Chernoff witness
       direction is at least as inflated -- projecting does NOT beat the energy; if anything the
       worst direction is MORE inflated). Hence the per-period MGF >= energy-controlled MGF.
  (V3) ratio worst-dir-M2r / energy-E_r is BOUNDED in [binom(2r,r)/4^r, 1] times a small factor,
       i.e. the worst directional moment is THETA(E_r) -- same growth, same wall.
"""
import cmath, math
import numpy as np
from math import comb

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; nn = phi; fac = []; d = 2
    while d*d <= nn:
        if nn % d == 0:
            fac.append(d)
            while nn % d == 0: nn //= d
        d += 1
    if nn > 1: fac.append(nn)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac): return g
    raise RuntimeError

def find_prime(n, beta, kmax=400000):
    target = int(round(n ** beta)); k0 = max(2, target // n)
    for k in range(k0, k0 + kmax):
        p = 1 + n*k
        if is_prime(p):
            m = (p-1)//n
            if m > 1 and n*n < p:
                mm = m
                while mm % 2 == 0: mm //= 2
                if mm > 1: return p
    return None

def periods_all(p, n):
    g = primitive_root(p); m = (p-1)//n
    h = pow(g, m, p)
    mu = []; c = 1
    for _ in range(n):
        mu.append(c); c = c*h % p
    mu = np.array(mu, dtype=np.int64)
    w = 2.0*math.pi/p
    etas = np.empty(m, dtype=np.complex128)
    gc = 1
    for cc in range(m):
        etas[cc] = np.sum(np.exp(1j*w*((gc*mu) % p)))
        gc = gc*g % p
    return etas, m

def avg_dir_moment(etas, r, ndir=2000):
    """(1/m) sum_c (1/2pi int X_c(zeta)^{2r} dzeta) by dense direction average."""
    acc = 0.0
    for k in range(ndir):
        th = 2*math.pi*k/ndir
        X = (np.conj(np.exp(1j*th))*etas).real
        acc += np.mean(X**(2*r))
    return acc/ndir

def worst_dir_moment(etas, r, ndir=720):
    """max over zeta of (1/m) sum_c X_c^{2r}  (the inflated direction)."""
    best = -1e18
    for k in range(ndir):
        th = math.pi*k/ndir
        X = (np.conj(np.exp(1j*th))*etas).real
        v = np.mean(X**(2*r))
        if v > best: best = v
    return best

print("="*100)
print("(V1) identity:  (1/m) sum_c avg_zeta X_c^{2r}  ==  (binom(2r,r)/4^r) * E_r(mu_n)")
print("(V2/V3) worst-dir M2r vs energy E_r  (worst dir does NOT beat the energy)")
print("="*100)
for n, beta in [(8,3.0),(16,3.0),(32,2.7),(16,3.5),(8,4.0)]:
    p = find_prime(n, beta)
    if p is None: continue
    etas, m = periods_all(p, n)
    print(f"\n n={n} p={p} m={m}")
    print(f"   {'r':>2} {'avg_dir':>12} {'C(r)*E_r':>12} {'rel.err':>9} | {'worst_dir':>12} {'E_r':>12} "
          f"{'worst/E_r':>9} {'C(r)':>7}")
    for r in (1,2,3,4):
        Cr = comb(2*r, r)/(4.0**r)                 # binom(2r,r)/4^r
        Er = float(np.mean(np.abs(etas)**(2*r)))    # additive energy E_r
        ad = avg_dir_moment(etas, r)
        relerr = abs(ad - Cr*Er)/(Cr*Er) if Cr*Er > 0 else float('nan')
        wd = worst_dir_moment(etas, r)
        print(f"   {r:>2} {ad:>12.4f} {Cr*Er:>12.4f} {relerr:>9.2e} | {wd:>12.4f} {Er:>12.4f} "
              f"{wd/Er:>9.4f} {Cr:>7.4f}")

print()
print("READING:")
print(" * rel.err ~ 1e-9 confirms the EXACT identity: the direction-averaged per-period 2r-moment")
print("   IS C(r)*E_r. The per-period directional MGF's moments are the additive energy, fixed.")
print(" * worst/E_r in [C(r), ~1]: the WORST direction (the Chernoff witness) is THETA(E_r) -- it")
print("   does NOT fall below the energy. So the per-period MGF inherits the E_r deep-moment wall.")
print(" * => the per-period MGF (SubGaussianMGF) reduces, term by term in its Taylor/moment")
print("   expansion, to bounding E_r to r ~ log m = the SAME standing additive-energy/BGK wall.")
