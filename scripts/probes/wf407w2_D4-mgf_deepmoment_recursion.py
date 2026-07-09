# -*- coding: utf-8 -*-
"""
wf407-w2 / D4-mgf : the DECISIVE test. The per-period directional MGF is shallow-Gaussian
(M4/3M2^2 ~ 0.9, prev probe). But the MGF at the OPTIMAL lambda = sqrt(2 log m / sigma^2)
probes moments of order k ~ log m -- the DEEP directional moments. Two questions:

 (C1) Do the DEEP directional moments M_{2r} = (1/m) sum_c (Re conj(zeta) eta_c)^{2r}
      stay Gaussian-controlled (M_{2r} <= (2r-1)!! sigma^{2r}) up to r ~ log m, the range the
      MGF needs?  OR do they inflate at r_max = 2 log_n p exactly like the ABSOLUTE energy
      E_r (the standing wall)?  This decides "fewer moments suffice" vs "same deep-moment wall".

 (D)  The Hasse-Davenport / Jacobi RECURSION on the SINGLE period. Is there a per-period
      moment recursion M_k(eta; F_q, n) -> M_k(eta; F_q, n/2)  (subgroup descent, the natural
      analogue of the energy dyadic tower) OR  M_k(eta; F_q, n) -> M_k(F_{q^t}) (field lift)
      with a BOUNDED n-independent multiplier? If yes, the MGF closes by induction WITHOUT the
      symmetric energy. If the recursion multiplier scatters / the deep moments inflate -> the
      per-period MGF reduces to the SAME deep-moment / BGK wall.

Key analytic fact to keep in view (EnergyCharacterTransport, in-tree, proven):
    (1/(p-1)) sum_{b!=0} |eta_b|^{2r} = E_r(mu_n)   [absolute even moment = additive energy]
so the ABSOLUTE per-period MGF == energy ladder == the wall. The only hope for "fewer moments"
is that the DIRECTIONAL (real-part) moments are strictly tamer. (C1) tests exactly that.
"""
import cmath, math
import numpy as np

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
    return etas, m, g, mu

def worst_dir(etas, ndir=360):
    best = -1e18; bth = 0.0
    for k in range(ndir):
        th = math.pi*k/ndir
        v = ((np.conj(np.exp(1j*th))*etas).real).max()
        if v > best: best = v; bth = th
    return (np.conj(np.exp(1j*bth))*etas).real

def dfact(k):  # (k-1)!! double factorial of ODD argument k-1 for even moment normalization
    r = 1.0
    j = k-1
    while j > 1:
        r *= j; j -= 2
    return r

print("="*104)
print("(C1)  DEEP directional even moments  M_{2r}/((2r-1)!! sigma^{2r})   [=1 Gaussian, >1 inflated]")
print("      sigma^2 = M_2 (empirical directional variance). r up to ~ log m.")
print("      Compare to ABSOLUTE energy ratio  E_r/((2r-1)!! n^r)  [the standing-wall object].")
print("="*104)

configs = [(8,3.0),(16,3.0),(32,2.7),(8,4.0),(16,3.5),(32,3.0),(64,2.5)]
for n, beta in configs:
    p = find_prime(n, beta)
    if p is None:
        print(f"n={n} no prime"); continue
    etas, m, g, mu = periods_all(p, n)
    X = worst_dir(etas)
    Xc = X - X.mean()
    s2 = Xc.var()
    rmax = max(2, int(round(math.log(m))))           # deep range the MGF probes
    rmax = min(rmax, 8)
    bval = math.log(p)/math.log(n)
    print(f"\n n={n} p={p} beta={bval:.2f} m={m}  sigma^2/n={s2/n:.3f}  (deep r up to {rmax})")
    dir_row = []
    abs_row = []
    for r in range(2, rmax+1):
        M2r = float(np.mean(Xc**(2*r)))
        dirr = M2r / (dfact(2*r) * s2**r)            # directional even-moment Gaussianity
        Er = float(np.mean(np.abs(etas)**(2*r)))     # absolute energy E_r
        absr = Er / (dfact(2*r) * (n**r))            # absolute-energy Gaussianity (= the wall)
        dir_row.append((r, dirr)); abs_row.append((r, absr))
    print("   r:        " + "  ".join(f"{r:>8d}" for r,_ in dir_row))
    print("   dir M2r:  " + "  ".join(f"{v:>8.3f}" for _,v in dir_row))
    print("   abs E_r:  " + "  ".join(f"{v:>8.3f}" for _,v in abs_row))

print()
print("="*104)
print("(D)  Hasse-Davenport / subgroup-descent recursion on the SINGLE period: does")
print("     M_k(eta; n) relate to M_k(eta; n/2) with a BOUNDED n-independent multiplier?")
print("     Test: SAME prime p, two nested dyadic subgroups mu_n > mu_{n/2}. Compare directional")
print("     moments. A clean recursion => bounded ratio independent of which moment.")
print("="*104)
for n, beta in [(16,3.5),(32,3.0),(64,2.5)]:
    p = find_prime(n, beta)
    if p is None: continue
    # mu_n and mu_{n/2} are both subgroups of F_p^* for the SAME p (n,n/2 | p-1).
    e_n, m_n, g, _ = periods_all(p, n)
    e_h, m_h, _, _ = periods_all(p, n//2)
    Xn = worst_dir(e_n); Xn = Xn - Xn.mean()
    Xh = worst_dir(e_h); Xh = Xh - Xh.mean()
    print(f"\n n={n}->{n//2}  p={p}  m_n={m_n} m_(n/2)={m_h}")
    print(f"   {'k':>3} {'M_k(n)':>11} {'M_k(n/2)':>11} {'ratio':>9} {'2^(k/2)':>9}")
    for k in (2,4,6,8):
        Mn = float(np.mean(Xn**k))
        Mh = float(np.mean(Xh**k))
        ratio = Mn/Mh if abs(Mh) > 1e-9 else float('nan')
        print(f"   {k:>3} {Mn:>11.2f} {Mh:>11.2f} {ratio:>9.3f} {2**(k/2):>9.3f}")
    print("   [bounded k-INDEPENDENT ratio = recursion exists; ratio tracking 2^(k/2)=variance")
    print("    scaling only, k-DEPENDENT spread = NO loss-free moment recursion]")
