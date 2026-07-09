#!/usr/bin/env python3
"""
C006 sub-claim: "the only open input is a SINGLE exponential moment (MGF), STRICTLY LESS than
the BGK all-moments wall."  Attack this structural claim directly (not just numerically).

ARGUMENT TO TEST.  The MGF is the generating function of the moments:
   Mhat(lambda) = (1/m) sum_c exp(lambda X_c) = sum_{k>=0} lambda^k mu_k / k!,
   mu_k = (1/m) sum_c X_c^k  (the empirical k-th moment of the directional projection).
A sigma^2 = O(n) sub-Gaussian MGF bound  Mhat(lambda) <= exp(sigma^2 lambda^2/2)  is EQUIVALENT
(up to universal constants) to the sub-Gaussian MOMENT bound
   mu_{2r} <= (2r-1)!! sigma^{2r}   for ALL r.
(standard: MGF<=exp(s lam^2/2) <=> ||X||_{psi2}<inf <=> mu_{2r}<=(2r)!/(2^r r!) s^r = (2r-1)!! s^r.)

So a "single MGF with sigma^2=O(n)" is NOT a single moment — it PACKAGES all even moments
mu_{2r} <= (2r-1)!! (O(n))^r.  That is EXACTLY the GaussianEnergyBound input the moment-method
file (GaussPeriodMomentBound.lean) calls the open core, restated:
   E_r(mu_n) = (1/q)... actually  m*mu_{2r}(directional) ~ relates to E_r(mu_n) <= (2r-1)!! n^r.
The MGF route's open input therefore IMPLIES the all-moments input. They are the SAME wall.

We verify the equivalence numerically: extract empirical even moments mu_{2r}/((2r-1)!! n^r)
from the REAL Gauss sequence, and the MGF sigma^2; show
  (i)  mu_{2r} <= (2r-1)!! sigma_mgf^{2r}  holds with the SAME sigma^2 the MGF gives, AND
  (ii) the all-moments ratio mu_{2r}/((2r-1)!! n^r) is ~O(1) up to r ~ log m  -- i.e. the MGF
       boundedness at lambda* is realized BY the moment bound holding to order r~lambda*^... .
The point: there is no regime where the MGF holds but a moment fails, or vice versa, for the
r that matters.  Conclusion feeds the verdict (REDUCED-to-same-wall, not strictly-less).
"""
import cmath, math
import statistics as st

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d*d <= x:
        if x % d == 0: return False
        d += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; fac = []; t = phi; d = 2
    while d*d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t//=d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac):
            return g
    return None

def gauss_periods(p, n, g):
    m = (p-1)//n
    gen = pow(g, m, p)
    mu = []; x = 1
    for _ in range(n):
        mu.append(x); x = (x*gen) % p
    e = [cmath.exp(2j*math.pi*k/p) for k in range(p)]
    etas = []
    bc = 1
    for c in range(m):
        s = 0j
        for x in mu:
            s += e[(bc*x) % p]
        etas.append(s)
        bc = (bc*g) % p
    return etas, m

def double_factorial(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

def main():
    print("# C006: is the SINGLE MGF strictly weaker than ALL even moments?  (equivalence test)")
    print("# sub-Gaussian MGF(sigma^2) <=> mu_{2r} <= (2r-1)!! sigma^{2r} for all r.")
    print("# If the MGF-sigma^2 reproduces the moment bound (and vice versa) they are the SAME wall.")
    print()
    # Use a thin n with a large prime (prize-like beta), one good case per n.
    cases = []
    for n in [8, 16, 32]:
        p = n
        best = None
        while p < 200000:
            p += 1
            if p % n != 1 or not is_prime(p): continue
            m = (p-1)//n
            if m < 2000: continue
            best = (p, m)
            if m > 8000: break
        if best: cases.append((n, best[0], best[1]))
    for (n, p, _) in cases:
        g = primitive_root(p)
        etas, m = gauss_periods(p, n, g)
        logm = math.log(m)
        beta = math.log(p)/math.log(n)
        # worst-direction analysis
        print(f"--- n={n} p={p} m={m} logm={logm:.2f} beta={beta:.2f} ---")
        lam_star = math.sqrt(2*logm/n)
        # MGF sigma^2 at lambda* (worst dir)
        worst_s2 = 0.0; worst_dir = 0
        dir_X = None
        for t in range(24):
            zeta = cmath.exp(2j*math.pi*t/24)
            X = [(zeta.conjugate()*e).real for e in etas]
            mu0 = st.mean(X); Xc = [x-mu0 for x in X]
            Mhat = st.mean(math.exp(lam_star*x) for x in Xc)
            if Mhat > 1:
                s2 = 2*math.log(Mhat)/(lam_star*lam_star)
                if s2 > worst_s2:
                    worst_s2 = s2; worst_dir = t; dir_X = Xc
        sigma2_mgf = worst_s2
        print(f"   lambda*={lam_star:.4f}  sigma2_mgf(worst dir #{worst_dir})/n = {sigma2_mgf/n:.4f}")
        # even moments on that worst direction
        print(f"   {'2r':>3} {'mu_2r':>14} {'(2r-1)!! n^r':>16} {'ratio(/n^r)':>12} {'(2r-1)!! sig_mgf^2r':>20} {'mu<=mgf?':>9}")
        for r in range(1, 9):
            k = 2*r
            mu_k = st.mean(x**k for x in dir_X)
            df = double_factorial(k-1)
            mom_bound = df * (n**r)
            mgf_bound = df * (sigma2_mgf**r)
            ratio = mu_k/(df*(n**r)) if df>0 else float('nan')
            ok = "yes" if mu_k <= mgf_bound*1.0001 else "NO"
            print(f"   {k:>3} {mu_k:14.3e} {mom_bound:16.3e} {ratio:12.4f} {mgf_bound:20.3e} {ok:>9}")
        print()
    print("# READ: if mu_2r <= (2r-1)!! sigma_mgf^{2r} holds for all r (col 'mu<=mgf?'=yes), the")
    print("#       single MGF ENCODES all even moments => it is the SAME object as GaussianEnergyBound,")
    print("#       not a strictly-weaker single moment.  The 'strictly less than BGK' claim is then FALSE;")
    print("#       the honest status is REDUCED-to-the-same-wall (repackaged), not a weaker input.")

if __name__ == "__main__":
    main()
