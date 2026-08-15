#!/usr/bin/env python3
"""
G233 (#466): basis-independent coefficient-L2 mass floor for the quotient-Jacobi fanout.

CONTEXT.  G228 rewrote the shared Mellin factor
    S_chi = sum_{u in G} conj(chi)(2-u),   What(chi) = n*S_chi
as the quotient-Jacobi column decomposition  S = V * 1  where
    V_lambda(chi) = (1/m) sum_{u in F_p*} lambda(u) conj(chi)(2-u)      (m x m over nontrivial chi).
G228/G229 gave a FIXED few-term / triangle floor K = Omega(sqrt m).
G231 (uncommitted G56) upgraded to the large-sieve operator bound lambda_max(V^H V) <= n^2,
hence any FIXED unit-weight K-COORDINATE subfamily needs K >= ceil((m-n)/(4n)) ~ 2^96 / 2^97.
G232 (Fable) checked empirically that no COHERENT eigen-subfamily helps either.

THIS RESULT.  A single closed, basis-INDEPENDENT inequality that subsumes all of the above.
Two exact inputs, sponsor regime 2 notin G:
    (A) large-sieve operator bound:   ||V a||^2 <= n^2 ||a||^2   for ALL a in C^H.
    (B) sponsor Parseval lower bound:  ||S||^2 = sum_{chi!=1}|S_chi|^2 >= n(m-n).
CLAIM.  Any coefficient vector a (sparse OR dense, coordinate subset OR coherent eigen-combination,
adaptive OR fixed) whose reconstruction V a captures a fraction f of ||S|| (||V a|| >= f ||S||) obeys
    ||a||^2 >= f^2 ||S||^2 / n^2 >= f^2 (m-n)/n.
For half capture f=1/2:  ||a||^2 >= (m-n)/(4n).  Division-free:  4 n ||a||^2 >= m - n.

WHY IT IS THE HONEST "incoherence" statement.  The pure K-dim subspace question is vacuous
(Eckart-Young: any line through S captures all of S), so no clean basis-free subspace theorem
exists.  The correct non-vacuous invariant is the COEFFICIENT L2 mass of the Jacobi-column
reconstruction: it bounds sparse unit-weight families (recovering G231's K >= (m-n)/4n as the
special case ||a||^2 = K) AND unbounded-weight coherent/eigen combinations by the same closed floor,
independent of any basis choice.  The load-bearing nontrivial fact is (A); (B) is exact Parseval.

This script verifies (A) [lambda_max(V^H V) <= n^2], (B) [||S||^2 >= n(m-n)], the identity S = V*1,
and the exact sponsor half-recovery mass floor 2^96 / 2^97.
"""
import math, numpy as np

def build(n, p):
    def isgen(g):
        x = 1; seen = set()
        for _ in range(p - 1):
            x = x * g % p; seen.add(x)
        return len(seen) == p - 1
    g = 2
    while not isgen(g):
        g += 1
    dlog = np.zeros(p, dtype=np.int64); x = 1
    for e in range(p - 1):
        dlog[x] = e; x = x * g % p
    m = (p - 1) // n
    Gset = set(pow(g, (m * k) % (p - 1), p) for k in range(n))
    twoInG = (2 % p) in Gset
    Hj = np.array([n * t for t in range(m)], dtype=np.int64)
    nz = Hj[Hj != 0]
    tau = 2j * math.pi / (p - 1)
    us = np.arange(1, p)
    t = (2 - us) % p
    nz_t = (t != 0)
    dlu = dlog[us]
    dlt = np.where(nz_t, dlog[t % p], 0)
    Lam = np.exp(tau * np.outer(Hj, dlu))          # (m, p-1)  lambda(u)
    Chi = np.exp(-tau * np.outer(nz, dlt)) * nz_t  # (|nz|, p-1)  conj chi(2-u)
    V = (Lam @ Chi.T).T / m                         # (|nz|, m)
    S = V.sum(axis=1)
    Garr = np.array(sorted(Gset))
    tG = (2 - Garr) % p
    nzG = (tG != 0)
    dlG = np.where(nzG, dlog[tG % p], 0)
    Sdef = (np.exp(-tau * np.outer(nz, dlG)) * nzG).sum(axis=1)
    reconErr = float(np.max(np.abs(S - Sdef)))
    Gram = V.conj().T @ V
    lam_max = float(np.max(np.linalg.eigvalsh(Gram)).real)
    normS2 = float(np.vdot(S, S).real)
    return dict(n=n, p=p, m=m, twoInG=twoInG, reconErr=reconErr,
                lam_max=lam_max, lam_max_over_n2=lam_max / n**2,
                normS2=normS2, parseval_lb=n * (m - n), floor=(m - n) / (4 * n))

def main():
    cells = [(16, 1297), (32, 2593), (8, 1009), (16, 3617), (32, 3617), (16, 4657)]
    ok = True
    for (n, p) in cells:
        r = build(n, p)
        A_ok = r['lam_max'] <= n**2 * (1 + 1e-9)
        B_ok = r['normS2'] >= r['parseval_lb'] * (1 - 1e-9) if not r['twoInG'] else True
        id_ok = r['reconErr'] < 1e-6
        ok = ok and A_ok and id_ok and (B_ok or r['twoInG'])
        print(f"n={r['n']} p={r['p']} m={r['m']} 2inG={r['twoInG']} reconErr={r['reconErr']:.1e} "
              f"lam_max/n^2={r['lam_max_over_n2']:.4f}(<=1:{A_ok}) "
              f"||S||^2={r['normS2']:.1f}>=n(m-n)={r['parseval_lb']}({B_ok}) "
              f"L2 half-floor (m-n)/4n={r['floor']:.2f}")
    # Sponsor exact constants
    n = 2**30
    m1 = 2**128 + 192
    m2 = 2**129 + 13
    def ceil_div(a, b):
        return -(-a // b)
    f1 = ceil_div(m1 - n, 4 * n)
    f2 = ceil_div(m2 - n, 4 * n)
    print()
    print(f"SPONSOR P1: half-recovery L2 mass floor ceil((m1-n)/4n) = {f1} = 2^{math.log2(f1):.3f} "
          f"(== 2^96: {f1 == 2**96})")
    print(f"SPONSOR P2: half-recovery L2 mass floor ceil((m2-n)/4n) = {f2} = 2^{math.log2(f2):.3f} "
          f"(== 2^97: {f2 == 2**97})")
    print(f"Division-free: 4n*||a||^2 >= m-n. P1: {m1-n}. P2: {m2-n}.")
    assert f1 == 2**96 and f2 == 2**97, "sponsor constants mismatch"
    assert ok, "a numeric input check failed"
    print("\nALL CHECKS PASS")

if __name__ == "__main__":
    main()
