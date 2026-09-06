"""Numerical census-to-maximum ratios for six finite subgroup spectra.

For eta_b = sum_{x in mu_n} exp(2*pi*i*b*x/p), the exact triangle inequality
gives |eta_b| <= n and the zero-frequency term is eta_0 = n. If an exact
nonzero maximum M occurs at K frequencies, then the nonzero 2r-moment is at
least K*M**(2r). Its unnormalized root therefore exceeds M when K>1 and M>0.
This finite-r gap does not rule out useful upper bounds above M, nor convergence
to M as r increases for a fixed finite spectrum.

This script computes complex floating-point sums for six (n,p) pairs and
r=1,...,6. K is a tolerance count within 1e-6 of the computed maximum, not an
exact multiplicity or certified orbit size. No exact census identities or
universal proximity-gap theorem are checked by this numerical replay.
"""
import cmath
import math


def prime_factors(n):
    f = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def spectrum(n, p):
    g = None
    pf = set(prime_factors(n))
    for cand in range(2, p):
        if pow(cand, n, p) == 1 and all(pow(cand, n // q, p) != 1 for q in pf):
            g = cand
            break
    if g is None:
        return None
    mu = [pow(g, k, p) for k in range(n)]
    return [abs(sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in mu))
            for b in range(p)]


def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2
        c += 1
    return c


cells = [(8, 257), (16, 257), (16, 65537), (32, 257), (32, 193), (32, 577)]
print("  n      p  v2    n      M   n>=M?  K(tol)  |  "
      "DC-subtracted (p*E_r - n^2r)^(1/2r)/M, r=1..6")
for n, p in cells:
    etas = spectrum(n, p)
    if etas is None:
        print(f"{n:>3}{p:>7}  no subgroup")
        continue
    M = max(etas[b] for b in range(1, p))
    K = sum(1 for b in range(1, p) if abs(etas[b] - M) < 1e-6)
    ndc = etas[0]
    ratios = []
    for r in range(1, 7):
        dcsub = sum(etas[b] ** (2 * r) for b in range(1, p))  # excludes b=0
        ext = dcsub ** (1.0 / (2 * r))
        ratios.append(ext / M)
    print(f"{n:>3}{p:>7}{v2(p-1):>4}{ndc:>6.1f}{M:>8.3f}   {ndc>=M-1e-9!s:>5}   {K:>6}      |  "
          + " ".join(f"{x:.4f}" for x in ratios))
