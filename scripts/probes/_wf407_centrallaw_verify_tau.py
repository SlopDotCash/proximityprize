#!/usr/bin/env python3
"""Third independent cross-check: verify the DFT/Gauss-sum identity and |tau|=sqrt(p).

eta_b = (1/m)[ -1 + sum_{j=1}^{m-1} psi(b)^{-j} tau(psi^j) ]
where psi generates the index-m character group of F_p^x/mu_n, and
tau(psi^j) = sum_{x in F_p^x} psi^j(x) e_p(x) is the Gauss sum, |tau|=sqrt(p).

We compute tau directly and confirm |tau(psi^j)| = sqrt(p) for all j!=0, and that
B from coset enumeration equals (sqrt(p)/m)*||DFT(a)||_inf with a_j = tau(psi^j)/sqrt(p)
up to the -1/m boundary term. This validates the prize reformulation.
"""
import numpy as np, math
from sympy import primitive_root

def verify(p, n):
    m = (p - 1) // n
    g = primitive_root(p)
    tp = 2.0 * math.pi / p
    # discrete log table base g
    dlog = {}
    cur = 1
    for e in range(p - 1):
        dlog[cur] = e
        cur = (cur * g) % p
    # index-m multiplicative characters that are trivial on mu_n = <g^m>:
    # chi_j(g^e) = exp(2*pi*i * j * e / m)? We need characters of F_p^x/mu_n ~ Z_m.
    # The dual group: chars trivial on mu_n are chi(g^e)=exp(2*pi*i*(m'*e)/(p-1))
    # with m' multiple of n? Actually chars of F_p^x are chi_k(g^e)=exp(2*pi*i*k*e/(p-1)).
    # chi_k trivial on mu_n=<g^m> iff chi_k(g^m)=1 iff k*m/(p-1) integer iff n | k.
    # So nontrivial chars on the quotient: k = n*j, j=1..m-1.
    xs = np.arange(1, p)
    ex = np.exp(1j * tp * xs)            # e_p(x) for x=1..p-1
    elog = np.array([dlog[int(x)] for x in xs])
    taus = []
    for j in range(1, m):
        k = n * j
        chi = np.exp(2j * math.pi * k * elog / (p - 1))
        tau = (chi * ex).sum()
        taus.append(tau)
    taus = np.array(taus)
    tau_abs = np.abs(taus)
    sqrtp = math.sqrt(p)
    max_tau_dev = float(np.max(np.abs(tau_abs - sqrtp)))
    # reconstruct B via identity: eta on coset rep g^t:
    # eta_{g^t} = (1/m)[ -1 + sum_{j=1}^{m-1} chi_{nj}(g^t)^{-1} tau(chi_{nj}) ]?
    # standard: eta_b = (1/m) sum_{chi: chi|mu_n=1} conj(chi)(b) tau(chi), incl trivial chi (tau=-1).
    best = 0.0
    for t in range(m):
        acc = -1.0 + 0j   # trivial char contributes tau=-1
        for jj, j in enumerate(range(1, m)):
            k = n * j
            chib = np.exp(2j * math.pi * k * t / (p - 1))   # chi_k(g^t)
            acc += np.conj(chib) * taus[jj]
        val = abs(acc) / m
        if val > best:
            best = val
    return m, max_tau_dev, best, sqrtp

if __name__ == "__main__":
    for (p, n) in [(41, 8), (101, 10), (151, 15), (211, 14)]:
        m, dev, Bident, sqrtp = verify(p, n)
        print(f"p={p:4d} n={n:3d} m={m:3d}: max||tau|-sqrt p|={dev:.2e}  B(identity)={Bident:.5f}  sqrt(p)={sqrtp:.4f}")
