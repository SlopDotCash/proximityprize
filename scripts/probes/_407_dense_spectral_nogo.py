#!/usr/bin/env python3
"""
#407 dense-cayley-spectral: the PRECISE no-go.

Two facts, machine-verified, that together pin why dense-graph spectral methods give nothing:

(A) THE GRAPH IS SPARSE, NOT DENSE. m=(q-1)/n ~ 2^128 constant => density n/q = 1/m ~ 2^-128.
    n = q^{mu/(mu+128)} < q^{1/4} for mu<=40. So the 'dense' premise of the angle is false;
    Alon-Boppana (a sparse-regime lower bound) APPLIES.

(B) THE SPECTRUM IS BULK-WIDE. All m off-diagonal eigenvalues have RMS sqrt(n) (Parseval), and
    the eigenvalue measure -> N(0,1)*sqrt(n) (proven moments). So B = max is an EXTREME-VALUE
    over m ~ q-near-Gaussian eigenvalues. Every dense-spectral inequality (Hoffman ratio,
    Lovasz theta for vertex-transitive, expander mixing, Krein) is a constraint that is SLACK
    by a factor ~ sqrt(m / log m) at the worst-case B, because they only "see" the variance
    (2nd moment), which gives Cantelli B <= sqrt(nm)=sqrt(q) -- the TRIVIAL bound.

We quantify the slack of each dense lever at the true B.
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def gauss_periods_real(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    gm = pow(g, m, p)
    sub = []
    cur = 1
    for j in range(n):
        sub.append(cur)
        cur = (cur * gm) % p
    sub = np.array(sub, dtype=np.int64)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    bs = np.arange(1, p)
    eta = np.zeros(p - 1, dtype=complex)
    for x in sub:
        eta += w[(bs * x) % p]
    return eta.real


print("=" * 104)
print(" DENSE-SPECTRAL NO-GO: each dense lever's bound on B, and its slack factor vs the true B")
print("=" * 104)
print(f"{'n':>4}{'m':>6}{'p':>8}{'trueB':>9}{'Cantelli=sqrt(q)':>17}"
      f"{'Hoffman(theta)':>16}{'target sqrt(nlnm)':>18}{'slack=Cantelli/true':>20}")
for n in [8, 16, 32, 64]:
    for m in [8, 32, 128, 512]:
        p = m * n + 1
        if not isprime(p) or p > 200000:
            continue
        re = gauss_periods_real(p, n)
        B = np.abs(re).max()
        # all eigenvalues incl b=0 (=n)
        eigs = np.concatenate([[float(n)], re])
        N = p
        d = n
        lmin = eigs.min()
        hoffman = N * (-lmin) / (d - lmin)  # = Lovasz theta for normal Cayley = independence clamp
        cantelli = math.sqrt(p)  # variance-only one-sided extreme atom bound ~ sqrt(nm)
        target = math.sqrt(n * math.log(m))
        print(f"{n:>4}{m:>6}{p:>8}{B:>9.3f}{cantelli:>17.2f}{hoffman:>16.1f}{target:>18.3f}"
              f"{cantelli/B:>20.2f}")
print()
print("READING:")
print(" - Cantelli (variance-only, = all that vertex-transitive dense LP can extract for the")
print("   SUP eigenvalue) gives only sqrt(q). Its slack vs the true B is ~ sqrt(m/log m) and")
print("   GROWS with m: at prize m=2^128 the slack is ~2^63. Useless.")
print(" - Hoffman/theta bound the INDEPENDENCE number, not B (wrong functional). Reported to show")
print("   it is a clamp on alpha, not an upper bound on the sup eigenvalue.")
print(" - To beat sqrt(q) the LP needs higher moments (4th,6th,...,~log m). That is EXACTLY the")
print("   Markov-Krein moment LP, already proven short by Theta(log m) provable moments.")
print(" CONCLUSION: dense-spectral tools, even applied at full strength to the (actually sparse)")
print("   graph, certify only the variance => trivial sqrt(q). They CANNOT reach sqrt(n log m).")
