#!/usr/bin/env python3
"""
C094_power_spectrum.py   (#407, connection C094)

CLAIM under test (C094):
  The tangent-house form B^2 = n + (sqrt(p)/m) * max_b |Sum_{h!=0} unit_h * T_h * chi^h(b)|,
  with unit_h = conj(tau_h)/sqrt(p), routes through the Gauss-quotient identity
        T_h = (conj(tau_h)/(m p)) * Sum_i tau_i * conj(tau_{i+h})
  so that (unit_h * T_h)_h IS (a normalized) autocorrelation of (tau_i).  By Wiener-Khinchin
  its b-DFT is therefore a POWER SPECTRUM = |eta_b|^2 (up to normalization/const), i.e. a
  MANIFESTLY-NONNEGATIVE, Parseval-EXACT restatement of the house -- "no L1 bound is tight".

We verify EXACTLY (proper-subgroup prize regime: dyadic mu_n, q prime =1 mod n, q ~ n^beta,
n << sqrt(q)) the chain of sub-claims:

  (I3)  A_h := Sum_j tau_j conj(tau_{j+h}) == m * chi^h(-1) * tau_{-h} * T_h        [already known]
  (G)   GAUSS-QUOTIENT form: T_h == (conj(tau_h)/(m p)) * A_h    for h != 0          [C094's key rewrite]
        -- i.e. unit_h * T_h == (1/(m p)) * A_h * (conj(tau_h)^2 / p) ??? we test the exact const.
  (S)   SPECTRUM: Sum_{h!=0} unit_h * T_h * chi^h(b)  reconstructs  c1*|eta_b|^2 - c0  EXACTLY
        for some n,q-independent real constants c1,c0 (the C094 headline; b-DFT = power spectrum).
  (NN)  the reconstructed object is REAL and NONNEGATIVE-up-to-the-affine-shift (power spectrum).
  (TIGHT) does the house B then admit a NON-trivial bound from this exact form, or does it
        weld back to BGK (max_b |eta_b| unbounded)?  Report B/sqrt(n ln m) and B vs 2 sqrt(n).
"""
import cmath, math, sympy

def primitive_root(p):
    return int(sympy.primitive_root(p))

def run(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    def psi(x): return cmath.exp(2j * math.pi * (x % p) / p)
    dlog = [0]*p
    cur = 1
    for k in range(p-1):
        dlog[cur] = k
        cur = (cur*g) % p
    def chi_pow(j, x):
        x %= p
        if x == 0: return 0.0
        return cmath.exp(2j*math.pi*(j*dlog[x])/m)
    mu = [pow(g, (m*t) % (p-1), p) for t in range(n)]

    # Gauss sums tau_j, j=0..m-1 ; |tau_j|=sqrt(p) for j!=0, tau_0=-1
    tau = []
    for j in range(m):
        s = 0j
        for x in range(1, p):
            s += chi_pow(j, x)*psi(x)
        tau.append(s)

    # eta_b at coset reps b=g^c, c=0..m-1
    def eta(c):
        b = pow(g, c, p)
        return sum(psi((b*w) % p) for w in mu)
    etas = [eta(c) for c in range(m)]

    # tangent sums T_h
    def T(h):
        return sum(chi_pow(h, (1-w) % p) for w in mu)
    Th = [T(h) for h in range(m)]

    # autocorrelation A_h = sum_j tau_j conj(tau_{j+h})
    A = [sum(tau[j]*tau[(j+h) % m].conjugate() for j in range(m)) for h in range(m)]

    # ---- (I3) A_h == m chi^h(-1) tau_{-h} T_h  (h!=0)
    err_I3 = 0.0
    for h in range(1, m):
        pred = m*chi_pow(h, p-1)*tau[(-h) % m]*Th[h]
        err_I3 = max(err_I3, abs(A[h]-pred))

    # ---- (G) Gauss-quotient: solve I3 for T_h => T_h = A_h /(m chi^h(-1) tau_{-h}).
    # C094 asserts a form T_h = (conj(tau_h)/(m p)) * A_h.  Test whether
    #   m chi^h(-1) tau_{-h}  ==  m p / conj(tau_h)   i.e.  chi^h(-1) tau_{-h} conj(tau_h) == p.
    # (Hasse-Davenport / tau_{-h} = chi^h(-1) conj(tau_h) when |tau_h|^2=p.)
    err_G = 0.0
    for h in range(1, m):
        lhs = chi_pow(h, p-1)*tau[(-h) % m]*tau[h].conjugate()
        err_G = max(err_G, abs(lhs - p))

    # so unit_h*T_h with unit_h=conj(tau_h)/sqrt(p):
    #   unit_h*T_h = (conj(tau_h)/sqrt(p)) * A_h/(m chi^h(-1) tau_{-h})
    #             = (conj(tau_h)/sqrt(p)) * A_h * conj(tau_h)/(m p)        [using (G)]
    #             = conj(tau_h)^2 * A_h / (m p sqrt(p)).
    unit = [tau[h].conjugate()/math.sqrt(p) for h in range(m)]
    uT = [unit[h]*Th[h] for h in range(m)]

    # ---- (S) house spectrum:  S_b := sum_{h!=0} unit_h T_h chi^h(b).
    # Test: does S_b reconstruct an affine function of |eta_b|^2 with n,q-indep constants?
    # From I2: |eta_b|^2 = (1/m^2) sum_h chi^h(b) A_h ; the h=0 term is A_0 = sum|tau_j|^2.
    # We FIT c1,c0 over b and report residual.  We ALSO test the *clean* prediction that comes from
    # the algebra (uT_h = conj(tau_h)^2 A_h/(m p sqrt p)) -- note this is NOT simply A_h, so the
    # b-DFT of uT is the DFT of  conj(tau_h)^2/(...) * A_h, a TWISTED autocorrelation, not |eta_b|^2.
    def S(c):
        b = pow(g, c, p)
        return sum(uT[h]*chi_pow(h, b) for h in range(1, m))
    Sb = [S(c) for c in range(m)]
    e2 = [abs(etas[c])**2 for c in range(m)]
    # imaginary part of S_b (should be ~0 iff it's a real power spectrum)
    max_imag_S = max(abs(z.imag) for z in Sb)

    # least-squares fit S_b.real ~ c1*e2 + c0  over b=0..m-1
    mr = m
    sx = sum(e2); sy = sum(z.real for z in Sb); sxx = sum(v*v for v in e2)
    sxy = sum(e2[c]*Sb[c].real for c in range(mr))
    denom = mr*sxx - sx*sx
    if abs(denom) > 1e-12:
        c1 = (mr*sxy - sx*sy)/denom
        c0 = (sy - c1*sx)/mr
        resid = max(abs(Sb[c].real - (c1*e2[c]+c0)) for c in range(mr))
    else:
        c1 = c0 = float('nan'); resid = float('nan')

    # ---- compare: the GENUINE power-spectrum reconstruction (I2), DFT of A_h:
    def e2_fromA(c):
        b = pow(g, c, p)
        return (1.0/m**2)*sum(chi_pow(h, b)*A[h] for h in range(m))
    err_I2 = max(abs(e2[c] - e2_fromA(c).real) for c in range(m))

    # house numerics (b!=0, i.e. c!=0)
    B = max(abs(etas[c]) for c in range(1, m)) if m > 1 else abs(etas[0])
    law = math.sqrt(n*math.log(max(m, 2)))
    return dict(p=p, n=n, m=m, err_I3=err_I3, err_G=err_G, err_I2=err_I2,
                max_imag_S=max_imag_S, fit_c1=c1, fit_c0=c0, fit_resid=resid,
                B=B, B_over_law=B/law if law > 0 else float('nan'),
                B_over_2sqrtn=B/(2*math.sqrt(n)))

def find_primes(n, count, start=2):
    out=[]; k=start
    while len(out) < count:
        p = k*n+1
        if sympy.isprime(p): out.append(p)
        k += 1
    return out

if __name__ == "__main__":
    print("# C094 power-spectrum verification (proper-subgroup prize regime, exact arithmetic)\n")
    print(f"{'p':>7} {'n':>4} {'m':>5} | {'errI3':>8} {'errG':>8} {'errI2':>8} | "
          f"{'imS':>8} {'fit_c1':>8} {'fit_c0':>9} {'fitResid':>9} | {'B':>7} {'B/law':>6} {'B/2sqn':>7}")
    # proper-subgroup PRIZE-shaped: q ~ n^4 (n << sqrt q). keep p tractable for exact double loops.
    for n in [8, 16, 32]:
        # pick primes near q ~ n^4 (proper subgroup, large index m=(q-1)/n)
        target = n**4
        ps = find_primes(n, 60, start=2)
        # choose 2 with q close to n^4 and tractable (<~70000)
        cand = sorted(ps, key=lambda p: abs(p-target))
        chosen = [p for p in cand if p <= 70000][:2]
        # ensure n < sqrt(q)
        chosen = [p for p in chosen if n < math.isqrt(p)]
        for p in chosen:
            r = run(p, n)
            print(f"{r['p']:>7} {r['n']:>4} {r['m']:>5} | {r['err_I3']:>8.1e} {r['err_G']:>8.1e} "
                  f"{r['err_I2']:>8.1e} | {r['max_imag_S']:>8.1e} {r['fit_c1']:>8.3f} {r['fit_c0']:>9.2f} "
                  f"{r['fit_resid']:>9.1e} | {r['B']:>7.3f} {r['B_over_law']:>6.3f} {r['B_over_2sqrtn']:>7.3f}")
    print("\nLegend: errI3/errG/errI2 should be ~1e-10 (exact identities). imS = max imag part of S_b")
    print("(=0 iff S_b is a real power spectrum). fitResid = residual of S_b.real ~ c1*|eta_b|^2 + c0.")
    print("B/2sqn>1 => non-Ramanujan (BGK wall). The 'no L1 tight' / spectral claim is about errG+imS+fitResid.")
