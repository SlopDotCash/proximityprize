#!/usr/bin/env python3
"""
sweep_A35_shaw_operator.py  —  Shaw-operator unification probe (#407 actionable A35)

Object under test (the operator formulation of the prize open input):

  D  = mu_n  =  the multiplicative subgroup of order n = 2^mu in F_p^*,  p prime, p == 1 mod n.
  S_D  =  convolution-by-1_D on the ADDITIVE group F_p^+
        =  adjacency matrix of the Cayley graph  Cay(F_p^+, D)  (circulant in the additive group).

We verify, on prize-shaped small cases:

  (E)  shawOp_eigen  :  for every additive character psi_b(x) = e_p(b*x),  psi_b is an eigenvector
       of S_D with eigenvalue  eta_b = sum_{d in D} e_p(-b*d)  (= conj of the Gauss period;
       |eta_b| is the Gauss-period magnitude).  i.e. spectrum(S_D) = { eta_b : b in F_p }.

  (P)  Parseval second moment :  sum_{b in F_p} |eta_b|^2 = n * p,  hence
       sum_{b != 0} |eta_b|^2 = n*p - n^2  (eta_0 = n).

  (H)  shaw_offdiag_moment_le (Holder) :  with  B = max_{b != 0} |eta_b| ,  for every integer M >= 1
       sum_{b != 0} |eta_b|^{2M}  <=  B^{2M-2} * (n*p - n^2).

  (B)  the open B-form conjecture  B <= sqrt(2) * sqrt(n)  -- REPORT only (this is the open input).
       We tabulate B / sqrt(n)  and  B / sqrt(2 n log(p/n))  across primes to show where it sits.

No closure is claimed: (E),(P),(H) are exact identities/inequalities (the substrate to be Lean-ified);
(B) is the open conjecture, reported numerically only.
"""

import cmath
import math


def mul_subgroup(p, n):
    """Return mu_n = order-n subgroup of F_p^*  (requires n | p-1)."""
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    # find a generator g of F_p^*
    def order(a):
        o, x = 1, a % p
        while x != 1:
            x = (x * a) % p
            o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p - 1:
            g = cand
            break
    h = pow(g, (p - 1) // n, p)          # element of order n
    D = []
    x = 1
    for _ in range(n):
        D.append(x)
        x = (x * h) % p
    assert len(set(D)) == n
    return sorted(D)


def eta(p, D, b):
    """Gauss period eigenvalue eta_b = sum_{d in D} e_p(-b d)."""
    return sum(cmath.exp(-2j * math.pi * (b * d % p) / p) for d in D)


def check_eigen(p, D):
    """(E) verify S_D psi_b = eta_b psi_b for a few random b, on the full additive group."""
    n = len(D)
    worst = 0.0
    for b in [0, 1, 2, 3, 7, p // 2, p - 1]:
        ev = eta(p, D, b)
        # check the eigen-equation at several points x:  (S_D psi_b)(x) = eta_b * psi_b(x)
        for x in [0, 1, 5, p - 1]:
            lhs = sum(cmath.exp(2j * math.pi * (b * ((x - d) % p) % p) / p) for d in D)
            rhs = ev * cmath.exp(2j * math.pi * (b * x % p) / p)
            worst = max(worst, abs(lhs - rhs))
    return worst


def run(p, n):
    D = mul_subgroup(p, n)
    eig_err = check_eigen(p, D)
    etas = [eta(p, D, b) for b in range(p)]
    mags2 = [abs(e) ** 2 for e in etas]
    parseval = sum(mags2)                       # should equal n*p
    off = sum(mags2[b] for b in range(p) if b != 0)   # n*p - n^2
    B = max(abs(etas[b]) for b in range(p) if b != 0)
    # (H) Holder moment bound for M = 1..4
    holder_ok = True
    holder_rows = []
    for M in range(1, 5):
        lhs = sum(mags2[b] ** M for b in range(p) if b != 0)
        rhs = (B ** (2 * M - 2)) * off
        holder_ok = holder_ok and (lhs <= rhs + 1e-6)
        holder_rows.append((M, lhs, rhs))
    sqrtn = math.sqrt(n)
    sqrt2n = math.sqrt(2 * n)
    logfac = math.sqrt(2 * n * math.log(p / n)) if p > n else float("nan")
    return {
        "p": p, "n": n, "eig_err": eig_err,
        "parseval": parseval, "expect_np": n * p,
        "off": off, "expect_off": n * p - n * n,
        "B": B, "B/sqrt(n)": B / sqrtn, "B/sqrt(2n)": B / sqrt2n,
        "B/sqrt(2n log(p/n))": B / logfac,
        "holder_ok": holder_ok, "holder_rows": holder_rows,
    }


if __name__ == "__main__":
    # prize-shaped: smooth (2-power) subgroup orders n, primes p == 1 mod n, a few "thin" p~n^2..n^3
    cases = [
        (17, 8), (97, 8), (193, 8),
        (97, 16), (193, 16), (257, 16), (1153, 16),
        (193, 32), (257, 32), (1153, 32), (3329, 32),
        (257, 64), (3329, 64), (7681, 64),
        (786433, 16),     # structured Fermat-ish prime, n=16
        (65537, 64),      # Fermat prime, high 2-adic valuation
        (65537, 128),
    ]
    print("=" * 100)
    print("A35 Shaw-operator probe: spectrum(Cay(F_p^+, mu_n)) = {eta_b}, Parseval, Holder moment collapse")
    print("=" * 100)
    all_eigen_ok = True
    all_parseval_ok = True
    all_holder_ok = True
    for (p, n) in cases:
        try:
            r = run(p, n)
        except AssertionError as e:
            print(f"skip p={p} n={n}: {e}")
            continue
        eigen_ok = r["eig_err"] < 1e-9
        parseval_ok = abs(r["parseval"] - r["expect_np"]) < 1e-6 and abs(r["off"] - r["expect_off"]) < 1e-6
        all_eigen_ok = all_eigen_ok and eigen_ok
        all_parseval_ok = all_parseval_ok and parseval_ok
        all_holder_ok = all_holder_ok and r["holder_ok"]
        print(f"\np={p:>7} n={n:>4}  (p/n={p/n:8.1f})")
        print(f"  (E) eigen-eq max err          = {r['eig_err']:.2e}   {'OK' if eigen_ok else 'FAIL'}")
        print(f"  (P) Parseval  sum|eta|^2       = {r['parseval']:.3f}  expect n*p={r['expect_np']}   {'OK' if parseval_ok else 'FAIL'}")
        print(f"      off-trivial sum_{{b!=0}}     = {r['off']:.3f}  expect n*p-n^2={r['expect_off']}")
        print(f"  (H) Holder moment bound        : {'OK (M=1..4)' if r['holder_ok'] else 'FAIL'}")
        for (M, lhs, rhs) in r["holder_rows"]:
            print(f"        M={M}: sum|eta|^{2*M} = {lhs:14.3f}  <=  B^{2*M-2}*off = {rhs:14.3f}")
        print(f"  (B) B=max_{{b!=0}}|eta_b|        = {r['B']:.4f}")
        print(f"      B/sqrt(n)                  = {r['B/sqrt(n)']:.4f}   (conj B<=sqrt(2)~1.414)")
        print(f"      B/sqrt(2n)                 = {r['B/sqrt(2n)']:.4f}")
        print(f"      B/sqrt(2 n log(p/n))       = {r['B/sqrt(2n log(p/n))']:.4f}")
    print("\n" + "=" * 100)
    print(f"SUMMARY: eigen identity {'ALL OK' if all_eigen_ok else 'FAILURES'} | "
          f"Parseval {'ALL OK' if all_parseval_ok else 'FAILURES'} | "
          f"Holder {'ALL OK' if all_holder_ok else 'FAILURES'}")
    print("(E),(P),(H) are the exact substrate to Lean-ify. (B) sqrt(2) conjecture: REPORT only (open).")
    print("=" * 100)
