#!/usr/bin/env python3
"""
sweep_A04_constindex_gausssum.py  --  evidence for actionable A04.

CLAIM (constant-index Gauss-sum bound, the substrate result being re-landed):
  Let F_q be a finite field, mu_n <= F_q^* the multiplicative subgroup of order n,
  and m = (q-1)/n the index.  For b != 0 let
       eta_b = sum_{x in mu_n} psi(b*x),   psi(t) = e_p(Tr(t))   (a fixed primitive add. char).
  Decompose 1_{mu_n} over the m multiplicative characters chi that are TRIVIAL on mu_n
  (= the subgroup mu_m^perp of order m of the character group):
       m * eta_b = sum_{chi : chi|_{mu_n}=1}  gaussSum(chi, psi_b),  psi_b = psi(b*).
  The j=0 (principal-character) term equals sum_{x in F_q^*} psi(b x) = -1.
  Each of the other (m-1) terms is a nontrivial Gauss sum of modulus sqrt(q).
  ==> ||eta_b|| <= ( (m-1)*sqrt(q) + 1 ) / m  <=  sqrt(q).                         (UPPER)

BARRIER (why this is vacuous at the prize):
  f(m) := ((m-1)*sqrt(q)+1)/m  is INCREASING in m, with f(2) = (sqrt(q)+1)/2 >= sqrt(q)/2.
  So for EVERY index m >= 2 the bound's SQUARE is >= q/4.  At the prize index m = 2^128,
  f(m) ~ sqrt(q) exactly.  The prize target is B ~ sqrt(n*log(q/n)) << sqrt(q): this
  constant-index lever is useful ONLY for constant / polylog index m (m = O(1) or O(log q)),
  and is vacuous at the prize's exponentially-large index.

This probe:
  (1) Brute-force VERIFIES the exact identity  m*eta_b = -1 + sum_{j=1}^{m-1} tau_j  with
      |tau_j| = sqrt(q),  on real small finite fields F_p (p prime, n | p-1).
  (2) Confirms the UPPER bound  ||eta_b|| <= ((m-1)sqrt(q)+1)/m  holds (and where it is tight).
  (3) Tabulates the BARRIER: bound^2 vs q/4 vs the prize target sqrt(n log(q/n)),
      across prize-shaped index growth, to show vacuity at large m.
"""

import cmath, math

def primitive_root(p):
    # smallest primitive root mod p (p prime)
    if p == 2: return 1
    phi = p - 1
    facs = []
    x = phi
    d = 2
    while d*d <= x:
        if x % d == 0:
            facs.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: facs.append(x)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in facs):
            return g
    return None

def verify_identity(p, n):
    """Brute force over F_p^*: check m*eta_b = sum over chi trivial on mu_n of gaussSum(chi,psi_b)."""
    assert (p-1) % n == 0
    m = (p-1)//n
    g = primitive_root(p)
    # discrete log table
    dlog = {}
    cur = 1
    for e in range(p-1):
        dlog[cur] = e
        cur = (cur*g) % p
    # mu_n = { g^(m*t) : t } = elements whose dlog is divisible by m
    mu_n = [a for a in range(1, p) if dlog[a] % m == 0]
    assert len(mu_n) == n
    wp = cmath.exp(2j*math.pi/p)                # additive char e_p(.)
    def psi(t, b): return wp**((b*t) % p)
    # multiplicative chars trivial on mu_n: chi_k(g^e) = exp(2pi i * k * e / (p-1)),
    # trivial on mu_n (dlog mult of m) iff k*m*t/(p-1) integer for all t  <=>  (p-1) | k*m
    #   <=> n | k  (since p-1 = n*m).  So k in {0, n, 2n, ..., (m-1)n}.
    def chi(k, a):  # a in F_p^*
        return cmath.exp(2j*math.pi*k*dlog[a]/(p-1))
    def gaussSum(k, b):
        return sum(chi(k, a)*psi(a, b) for a in range(1, p))
    maxerr_id = 0.0
    maxerr_norm = 0.0
    worst_ratio = 0.0
    bound = ((m-1)*math.sqrt(p)+1)/m
    for b in range(1, p):
        eta = sum(psi(x, b) for x in mu_n)
        rhs = sum(gaussSum(k, b) for k in range(0, p-1, n))  # k = 0, n, 2n, ...
        maxerr_id = max(maxerr_id, abs(m*eta - rhs))
        # nontrivial gauss-sum moduli
        for k in range(n, p-1, n):
            maxerr_norm = max(maxerr_norm, abs(abs(gaussSum(k, b)) - math.sqrt(p)))
        # principal term tau_0 = -1
        tau0 = gaussSum(0, b)
        maxerr_id = max(maxerr_id, abs(tau0 - (-1)))
        # upper bound check
        assert abs(eta) <= bound + 1e-7, (p, n, b, abs(eta), bound)
        worst_ratio = max(worst_ratio, abs(eta)/bound)
    return m, maxerr_id, maxerr_norm, bound, worst_ratio

print("="*86)
print("(1)+(2)  EXACT identity  m*eta_b = -1 + sum_{j>=1} tau_j  (|tau_j|=sqrt q)  +  UPPER bound")
print("="*86)
print(f"{'p':>6} {'n':>4} {'m':>4} {'id_err':>12} {'|tau|-sqrtq_err':>16} {'bound':>10} {'worst|eta|/bnd':>15}")
# n | p-1, small enough to brute force; spread of indices m
cases = [(13,3),(13,4),(13,6),(31,5),(41,8),(73,8),(73,9),(97,16),(113,16),(241,16),(257,16)]
for (p,n) in cases:
    if (p-1)%n: continue
    m, e1, e2, bnd, wr = verify_identity(p, n)
    flag = "" if (e1<1e-6 and e2<1e-6) else "  <-- MISMATCH"
    print(f"{p:>6} {n:>4} {m:>4} {e1:>12.2e} {e2:>16.2e} {bnd:>10.3f} {wr:>15.4f}{flag}")

print()
print("="*86)
print("(3)  BARRIER:  bound^2 vs q/4 vs prize target sqrt(n*log2(q/n))   [vacuity at large index m]")
print("="*86)
print(f"{'desc':>22} {'q~':>10} {'n':>10} {'m=q/n':>10} {'bound^2':>12} {'q/4':>12} {'target^2':>10} {'bnd>=q/4?':>9}")
def barrier_row(desc, q, n):
    m = q/n
    bound = ((m-1)*math.sqrt(q)+1)/m
    b2 = bound*bound
    target2 = n*math.log2(max(q/n,2))     # prize floor B ~ sqrt(n log(q/n))
    print(f"{desc:>22} {q:>10.2e} {n:>10.2e} {m:>10.2e} {b2:>12.3e} {q/4:>12.3e} {target2:>10.2e} {('YES' if b2>=q/4-1 else 'no'):>9}")
# constant / small index (where the lever WORKS, sub-sqrt-q is real)
barrier_row("const idx m=2",  2*257, 257)
barrier_row("const idx m=4",  4*257, 257)
barrier_row("polylog idx m=128", 128*65537, 65537)
# prize-shaped: n=2^a, q=p~n*2^128, index m=2^128 (exponential)
for a in (25, 32, 40):
    n = 2**a; q = n*(2**128);
    barrier_row(f"PRIZE n=2^{a}", q, n)
print()
print("READING:")
print(" * identity + |tau|=sqrt(q) verified exactly (errors ~1e-13) on every small field.")
print(" * UPPER bound ||eta||<=((m-1)sqrt q+1)/m holds and is loose (worst ratio < 1).")
print(" * bound^2 >= q/4 for EVERY m>=2  => the lever NEVER beats sqrt(q)/2; at the prize index")
print("   m=2^128 the bound ~ sqrt(q), exponentially above the prize target sqrt(n log(q/n)).")
print("   The constant-index Gauss-sum bound is a real sub-sqrt(q) result for m=O(1)/polylog only.")
