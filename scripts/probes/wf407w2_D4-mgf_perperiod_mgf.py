# -*- coding: utf-8 -*-
"""
wf407-w2 / D4-mgf : PER-PERIOD sub-Gaussian MGF via a Hasse-Davenport / Jacobi-sum
RECURSION on the SINGLE period eta_b (NOT the symmetric energy E_r, NOT the average
tangent sum T).

The named open input (SalemZygmundChaining.lean, SubGaussianMGF):
    (1/m) sum_c exp(lam * Re(conj(zeta) * eta_c)) <= exp(sigma^2 lam^2 / 2)   (*)
with sigma^2 = O(n), uniform in (n,m,zeta). Then chernoff_max_re_le gives
B <= sqrt(2 sigma^2 log m) = the prize floor.

Wave-1 already established:
 - the AVERAGE tangent sum T (C070) carries the SAME sqrt(ln m) bulk-vs-tail gap and the
   Hasse-Davenport lift gives NO bounded multiplier for T (T'/T spread >10x). REFUTED there.
 - the EVT route (T232-08-evt) walls: exchangeability + 2 moments are insufficient; you need
   ALL higher moments = SubGaussianMGF.

THIS THREAD asks a DIFFERENT question: forget the average T. The MGF (*) is a statement about
the EMPIRICAL DISTRIBUTION of the m periods {eta_c}_c. Its k-th cumulant/moment is
    M_k := (1/m) sum_c (Re conj(zeta) eta_c)^k.
The MGF needs ALL M_k. The bet: a Hasse-Davenport / Jacobi recursion on the SINGLE period
eta_b relates the period MOMENTS M_k to lower-n period data, closing the MGF with FEWER than the
full energy ladder. Concretely test:

 (A) Is the per-period directional MGF cleanly sub-Gaussian with a UNIVERSAL constant C
     (sigma^2 = C n)?  Measure C := max over lam in [0,lam_max] of  2*psi(lam)/(n lam^2),
     psi(lam)=log[(1/m) sum_c exp(lam Re conj(zeta) eta_c)], worst direction zeta.
     Does C stay bounded as m grows at fixed n? (this is exactly what (*) needs.)

 (B) The MOMENT identity. The empirical moments of the period family are EXACTLY the
     symmetric additive energies (up to the direction zeta). Specifically for the FULL
     (all-b) family eta_b = sum_{y in mu_n} e_p(b y), the 2r-th absolute moment
        (1/(p-1)) sum_{b != 0} |eta_b|^{2r} = E_r(mu_n)   (the additive energy)
     by EnergyCharacterTransport. So the per-period MGF of |eta|^2 IS the energy ladder.
     => the per-period MGF over ABSOLUTE VALUE is NOT a different decomposition: it is the
     same E_r wall. We test whether the DIRECTIONAL (real-part) moments are GENUINELY easier
     (lower) than the absolute moments -- i.e. does projecting onto a direction zeta kill the
     deep-moment inflation?

 (C) The Hasse-Davenport recursion. The single Gauss sum tau(chi) lifts multiplicatively
     (tau(chi o Norm) = -(-tau(chi))^t over F_{q^t}). Does a per-period MOMENT M_k(eta over F_q)
     descend to M_k over a subfield / lower-n family with a BOUNDED, n-independent multiplier?
     If yes -> recursion closes the MGF. If the moment ratio scatters / tracks sqrt(field) ->
     same generic wall.

PRIZE REGIME: dyadic mu_n, n=2^mu, q ~ n^beta, n << sqrt(q). EXACT enumeration n=8,16,32(,64).
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
    target = int(round(n ** beta))
    k0 = max(2, target // n)
    for k in range(k0, k0 + kmax):
        p = 1 + n*k
        if is_prime(p):
            m = (p-1)//n
            if m > 1 and n*n < p:
                # require odd part of m > 1 so mu_n is a genuine proper dyadic subgroup
                mm = m
                while mm % 2 == 0: mm //= 2
                if mm > 1:
                    return p
    return None

def periods_all(p, n):
    """eta_b for ALL b in 1..p-1 (m distinct coset values). Returns the m distinct period
       values (one per coset) AND the per-coset count (= n each), via coset reps g^c."""
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

def worst_dir_proj(etas, ndir=360):
    best = -1e18; bth = 0.0
    for k in range(ndir):
        th = math.pi*k/ndir
        X = (np.conj(np.exp(1j*th))*etas).real
        v = X.max()
        if v > best: best = v; bth = th
    return bth, (np.conj(np.exp(1j*bth))*etas).real

def mgf_const_C(X, n, lam_max, ngrid=40):
    """C := max_lam 2 psi(lam)/(n lam^2), psi=log mean exp(lam X). centered X."""
    Xc = X - X.mean()
    worst = 0.0
    for lam in np.linspace(lam_max/ngrid, lam_max, ngrid):
        psi = math.log(np.mean(np.exp(lam*Xc)))
        worst = max(worst, 2*psi/(n*lam*lam))
    return worst

def directional_moments(X, ks):
    """centered directional moments M_k = (1/m) sum (X-mean)^k."""
    Xc = X - X.mean()
    return {k: float(np.mean(Xc**k)) for k in ks}

def abs_energy(etas, r):
    """E_r-style: (1/m) sum_c |eta_c|^{2r}  (the absolute even moment = additive energy)."""
    return float(np.mean(np.abs(etas)**(2*r)))

print("="*100)
print("D4-mgf  (A) per-period sub-Gaussian constant C (sigma^2=Cn) + plateau in m;")
print("        (B) directional real moments vs absolute |eta|^2 energy moments")
print("="*100)
print(f"{'n':>4} {'p':>9} {'beta':>5} {'m':>7} {'B':>8} {'C(MGF)':>8} {'M2/n':>7} {'M4/n^2':>8} "
      f"{'(M4/3M2^2)':>11} {'E2/n^2':>8} {'kurt_abs':>9}")
configs = [(8,3.0),(16,3.0),(32,2.7),(64,2.5),(8,4.0),(16,3.5),(32,3.0)]
for n, beta in configs:
    p = find_prime(n, beta)
    if p is None:
        print(f"{n:>4}  no prime near beta={beta}"); continue
    etas, m, g, mu = periods_all(p, n)
    B = float(np.abs(etas).max())
    th, X = worst_dir_proj(etas)
    var = X.var()
    lam_max = 3.0/math.sqrt(var) if var > 0 else 1.0
    C = mgf_const_C(X, n, lam_max)
    Ms = directional_moments(X, [2,4,6])
    M2, M4 = Ms[2], Ms[4]
    # Gaussianity ratio M4/(3 M2^2): =1 for Gaussian, >1 heavy directional tail
    gr = M4/(3*M2*M2) if M2 > 0 else float('nan')
    E2 = abs_energy(etas, 1)            # = (1/m) sum |eta|^2
    E2b = abs_energy(etas, 2)           # = (1/m) sum |eta|^4
    kurt_abs = E2b/(E2*E2) if E2 > 0 else float('nan')  # absolute-moment kurtosis
    bval = math.log(p)/math.log(n)
    print(f"{n:>4} {p:>9} {bval:>5.2f} {m:>7} {B:>8.3f} {C:>8.3f} {M2/n:>7.3f} {M4/(n*n):>8.3f} "
          f"{gr:>11.3f} {E2/(n*n):>8.3f} {kurt_abs:>9.3f}")

print()
print("INTERPRETATION (A/B):")
print(" * C(MGF) bounded & ~O(1) across all (n,m) => per-period directional MGF IS sub-Gaussian")
print("   with sigma^2=Cn EMPIRICALLY. This is what SubGaussianMGF needs (but measured, not proven).")
print(" * M4/(3 M2^2): directional 4th-moment Gaussianity. ~1 => directional projection is")
print("   near-Gaussian (the projection KILLS deep-moment inflation). >>1 => directional tail")
print("   still heavy = same wall in disguise.")
print(" * kurt_abs = E_2/(E_1)^2 absolute kurtosis (the energy-ladder object). Compare to the")
print("   directional gr: if directional gr << kurt_abs, projecting genuinely helps (different")
print("   decomposition); if comparable, the per-period MGF carries the SAME energy inflation.")
