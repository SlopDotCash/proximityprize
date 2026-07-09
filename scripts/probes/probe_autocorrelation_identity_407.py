#!/usr/bin/env python3
"""
probe_autocorrelation_identity_407.py  (#407)

Verifies a NEW exact identity for the power spectrum of the Gauss period
(incomplete subgroup sum) and tests whether the 2-power structure of mu_n gives
any EXTRA cancellation that could escape the sqrt-cancellation wall.

Setup: F_p prime, n = 2^a | p-1, m = (p-1)/n, chi a multiplicative character of
order m, mu_n = ker(chi) = order-n subgroup, psi(x) = e_p(x) additive char.

Objects:
  eta_b   = sum_{x in mu_n} psi(b x)                         (Gauss period; b in Z/m coset reps)
  tau_j   = sum_{x!=0} chi^j(x) psi(x)                       (Gauss sum, |tau_j|=sqrt(p), tau_0=-1)
  A_h     = sum_{j} tau_j conj(tau_{j+h})                    (autocorrelation of the Gauss-sum sequence)
  T_h     = sum_{w in mu_n} chi^h(1-w)                       (subgroup TANGENT character sum)
  J(i,h)  = sum_{u+v=1} chi^i(u) chi^h(v)                    (Jacobi sum)

Claimed identities (derived this session):
  (I1)  eta_b      = (1/m) sum_{j=0}^{m-1} chi^{-j}(b) tau_j
  (I2)  |eta_b|^2  = (1/m^2) sum_h chi^h(b) A_h
  (I3)  A_h        = m * chi^h(-1) * tau_{-h} * T_h          (h != 0 mod m)  <-- the new identity
  (I4)  T_h        = (1/m) sum_{i=0}^{m-1} J(chi^i, chi^h)

Escape test: max_h |T_h| / sqrt(n).  If ~ const (generic sqrt-cancellation), no escape.
"""

import cmath, math
import sympy

def primitive_root(p):
    return int(sympy.primitive_root(p))

def run(p, n):
    assert (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)               # generator of F_p^*
    # additive char psi(x) = exp(2pi i x / p)
    def psi(x): return cmath.exp(2j * math.pi * (x % p) / p)
    # multiplicative char chi of order m: chi(g^k) = exp(2pi i k / m).
    # build discrete log table
    dlog = [0] * p
    cur = 1
    for k in range(p - 1):
        dlog[cur] = k
        cur = (cur * g) % p
    def chi_pow(j, x):                   # chi^j(x), x in F_p^*
        x %= p
        if x == 0: return 0.0
        return cmath.exp(2j * math.pi * (j * dlog[x]) / (p - 1))  # chi(x)=exp(2pi i dlog/(p-1))^? see note
    # NOTE: chi has order m. chi(g)=exp(2pi i /m). g^k -> exp(2pi i k/m).
    def chi_pow_fixed(j, x):
        x %= p
        if x == 0: return 0.0
        k = dlog[x]
        return cmath.exp(2j * math.pi * (j * k) / m)
    chi_pow = chi_pow_fixed

    # subgroup mu_n = { g^{m*t} : t=0..n-1 }
    mu = [pow(g, (m * t) % (p - 1), p) for t in range(n)]
    mu_set = set(mu)

    # Gauss sums tau_j, j=0..m-1
    tau = []
    for j in range(m):
        s = 0j
        for x in range(1, p):
            s += chi_pow(j, x) * psi(x)
        tau.append(s)

    # eta_b for coset reps b = g^{0..m-1} (nonzero cosets); also b ranges Z/m index
    # represent coset by exponent c in 0..m-1: b = g^c
    def eta_direct(c):
        b = pow(g, c, p)
        return sum(psi((b * w) % p) for w in mu)
    def eta_dft(c):
        # (1/m) sum_j chi^{-j}(b) tau_j ; chi^{-j}(g^c)=exp(-2pi i j c/m)
        return (1.0 / m) * sum(cmath.exp(-2j * math.pi * (j * c) / m) * tau[j] for j in range(m))

    err_I1 = max(abs(eta_direct(c) - eta_dft(c)) for c in range(m))

    # |eta_b|^2 via I2
    A = []
    for h in range(m):
        s = 0j
        for j in range(m):
            s += tau[j] * (tau[(j + h) % m]).conjugate()
        A.append(s)
    def eta2_spec(c):
        return (1.0 / m**2) * sum(cmath.exp(2j * math.pi * (h * c) / m) * A[h] for h in range(m))
    err_I2 = max(abs(abs(eta_direct(c))**2 - eta2_spec(c).real) for c in range(m))

    # T_h
    def T(h):
        return sum(chi_pow(h, (1 - w) % p) for w in mu)   # w=1 -> chi(0)=0 auto
    Th = [T(h) for h in range(m)]

    # Jacobi sums J(i,h) = sum_{u} chi^i(u) chi^h(1-u)
    def J(i, h):
        return sum(chi_pow(i, u) * chi_pow(h, (1 - u) % p) for u in range(p))
    # I4: T_h = (1/m) sum_i J(i,h)
    err_I4 = max(abs(Th[h] - (1.0/m)*sum(J(i, h) for i in range(m))) for h in range(m))

    # I3: A_h = m chi^h(-1) tau_{-h} T_h   (h!=0)
    def chih_minus1(h):
        return chi_pow(h, (p - 1) % p)    # chi^h(-1)
    err_I3 = 0.0
    for h in range(1, m):
        pred = m * chih_minus1(h) * tau[(-h) % m] * Th[h]
        err_I3 = max(err_I3, abs(A[h] - pred))

    # house and law
    house = max(abs(eta_direct(c)) for c in range(1, m)) if m > 1 else abs(eta_direct(0))
    # the b=0 coset (c=0) is the principal one: eta_0 = sum psi(w) over mu, not n. exclude trivial only if b=0.
    house_all = max(abs(eta_direct(c)) for c in range(m))
    law = math.sqrt(n * math.log2(max(m,2)))
    # T_h escape test
    maxT = max(abs(Th[h]) for h in range(1, m)) if m > 1 else abs(Th[0])
    avgT = sum(abs(Th[h]) for h in range(1, m)) / max(m-1,1) if m > 1 else abs(Th[0])

    # tangent-house constant: max_h|T_h| / sqrt(n ln m), to compare against the additive
    # house constant C = B/sqrt(n ln m).  If they track, T_h IS the house (exact equivalence).
    lawln = math.sqrt(n * math.log(max(m, 2)))   # natural-log normalization (matches campaign C)
    return dict(p=p, n=n, m=m, err_I1=err_I1, err_I2=err_I2, err_I3=err_I3, err_I4=err_I4,
                house=house_all, law=law, ratio=house_all/law if law>0 else float('nan'),
                maxT=maxT, maxT_over_sqrtn=maxT/math.sqrt(n), avgT_over_sqrtn=avgT/math.sqrt(n),
                C_house=house_all/lawln if lawln>0 else float('nan'),
                C_tangent=maxT/lawln if lawln>0 else float('nan'))

def find_primes(n, count, start=None):
    # primes p with n | p-1, p prime, p not too large for exact loops (p up to ~5000)
    out = []
    k = (start or 2)
    while len(out) < count:
        p = k * n + 1
        if sympy.isprime(p):
            out.append(p)
        k += 1
    return out

if __name__ == "__main__":
    print("# Autocorrelation identity verification + 2-power escape test (#407)\n")
    print(f"{'p':>6} {'n':>4} {'m':>5} | {'errI1':>9} {'errI2':>9} {'errI3':>9} {'errI4':>9} | "
          f"{'house':>7} {'law':>7} {'rt':>5} | {'C_house':>7} {'C_tangent':>9}")
    for n in [4, 8, 16, 32]:
        # pick a few primes with varying index m, keep p modest
        ps = find_primes(n, 4, start=2)
        # add one larger-index prime for the escape test
        ps += find_primes(n, 1, start=40)
        for p in ps:
            if p > 6000:   # keep exact double loops tractable
                continue
            r = run(p, n)
            print(f"{r['p']:>6} {r['n']:>4} {r['m']:>5} | {r['err_I1']:>9.1e} {r['err_I2']:>9.1e} "
                  f"{r['err_I3']:>9.1e} {r['err_I4']:>9.1e} | {r['house']:>7.3f} {r['law']:>7.3f} "
                  f"{r['ratio']:>5.2f} | {r['C_house']:>7.3f} {r['C_tangent']:>9.3f}")
    print("\n(C_house = B/sqrt(n ln m); C_tangent = max|T_h|/sqrt(n ln m) — if they track, T_h IS the house)")
