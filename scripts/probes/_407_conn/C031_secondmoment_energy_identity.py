#!/usr/bin/env python3
"""
C031 attack: "CS25 second moment IS the additive energy E_2; n^{1/2} deficit wall."

The connection claims:
 (A) The CS25 second moment sum  E[N^2] = |C| * sum_{v in C} ballInterCount(r, v)
     "literally computes E_2 of the RS code".
 (B) The diagonal term I(0)=V is "the +V (n-scale) floor no L^2 method removes",
     i.e. it IS the additive-energy n^{1/2} deficit wall (list >= n^{3/2}).
 (C) Probe (mu_8/mu_16, p=12289) off-diag/diag at WINDOW radius is Theta(1).

We test each claim with exact integer arithmetic.

DEFINITIONS (from the Lean files, exactly):
  closeCount_C(r,w) = #{c in C : Hdist(w,c) <= r}
  E[N^2]            = sum_w closeCount(r,w)^2
                    = |C| * sum_{v in C} I(v)      (additive code)
  I(v) = ballInterCount(r,v) = #{x : Hdist(x,0)<=r and Hdist(x,v)<=r}
  V    = I(0)                = #{x : Hdist(x,0)<=r}   (the diagonal term, =ball volume)

ADDITIVE ENERGY E_2 of a SET S in an abelian group:
  E_2(S) = #{(a,b,c,d) in S^4 : a+b = c+d}
  diagonal of E_2 = solutions with {a,b}={c,d}, gives the |S|^2 floor (Cauchy-Schwarz).
  E_2(S) >= |S|^2  always; list-size sqrt(n*E) story is about S = mu_n (subgroup of F_q*).

The question: is the CS25 ball-intersection second moment the SAME object as E_2(mu_n)?
"""

import itertools
from math import comb

def hdist(x, y):
    return sum(1 for a, b in zip(x, y) if a != b)

def hnorm(x):
    return sum(1 for a in x if a != 0)

# ----------------------------------------------------------------------
# Part 1: exact CS25 second-moment quantities for a small RS-like code.
# We use a literal small linear MDS code over F_q in (ι->F) and compute
# E[N^2], V=I(0), and the off-diagonal, brute force, to check the Lean identities
# AND the diagonal floor structure.
# ----------------------------------------------------------------------

def all_vectors(F, n):
    return list(itertools.product(F, repeat=n))

def rs_code(q, n, k):
    """Reed-Solomon code: evaluations of deg<k polys at n distinct points (first n elts of F_q).
       Returns list of codewords as tuples in F_q^n. Requires n<=q."""
    pts = list(range(n))  # eval points 0..n-1 in Z_q  (must be distinct, n<=q)
    code = []
    for coeffs in itertools.product(range(q), repeat=k):
        cw = tuple(sum(coeffs[j]*pow(p, j, q) for j in range(k)) % q for p in pts)
        code.append(cw)
    return code

def ball_inter(F, n, r, v):
    """I(v) = #{x in F^n : Hdist(x,0)<=r and Hdist(x,v)<=r}."""
    cnt = 0
    zero = tuple(0 for _ in range(n))
    for x in itertools.product(F, repeat=n):
        if hdist(x, zero) <= r and hdist(x, v) <= r:
            cnt += 1
    return cnt

def second_moment_direct(F, n, code, r):
    """E[N^2] = sum_w closeCount(w)^2, brute over all w in F^n."""
    tot = 0
    for w in itertools.product(F, repeat=n):
        cc = sum(1 for c in code if hdist(w, c) <= r)
        tot += cc*cc
    return tot

def main():
    print("="*78)
    print("PART 1: verify Lean identity E[N^2] = |C| * sum_{v in C} I(v), and diag = V")
    print("="*78)
    # tiny exact instance: F_5, n=4, k=2 (RS[5,4,2], rate 1/2). |F^n| = 625.
    q, n, k = 5, 4, 2
    F = list(range(q))
    code = rs_code(q, n, k)
    print(f"RS[F_{q}, n={n}, k={k}]  |code|={len(code)}  (expect {q**k})")
    for r in range(0, n+1):
        EN2 = second_moment_direct(F, n, code, r)
        # right side
        sum_I = sum(ball_inter(F, n, r, v) for v in code)
        rhs = len(code) * sum_I
        I0 = ball_inter(F, n, r, tuple(0 for _ in range(n)))  # = V
        # off-diagonal = sum over v != 0
        offdiag = sum(ball_inter(F, n, r, v) for v in code if any(x != 0 for x in v))
        # global normalizer V^2 = sum over ALL v
        sumI_all = sum(ball_inter(F, n, r, v) for v in itertools.product(F, repeat=n))
        V = I0
        ratio = (offdiag / V) if V else float('nan')
        print(f" r={r}: E[N^2]={EN2:>7}  |C|*sumI={rhs:>7}  match={EN2==rhs}"
              f" | V=I(0)={V:>4}  offdiag={offdiag:>6}  off/diag={ratio:6.3f}"
              f" | sum_all I = {sumI_all} (V^2={V*V}) match={sumI_all==V*V}")

    print()
    print("="*78)
    print("PART 2: is the CS25 ball-intersection 'E_2' the SAME as E_2(mu_n) of the subgroup?")
    print("="*78)
    print("E_2(S) := #{(a,b,c,d) in S^4 : a+b=c+d}, S = mu_n subgroup of F_q*.")
    print("This is a count of ADDITIVE QUADRUPLES; it lives in F_q, dim 1.")
    print("The CS25 sum_{v in C} I(v) lives in F_q^n (the codeword space, dim n),")
    print("and I(v) is a HAMMING ball intersection, NOT an additive-quadruple count.")
    print()
    # exact E_2 of mu_n for several proper-subgroup primes (prize-shaped: n<<sqrt q)
    def e2_subgroup(q, n):
        g = primitive_root(q)
        order = q-1
        assert order % n == 0
        step = order // n
        mu = sorted({pow(g, step*i, q) for i in range(n)})
        assert len(mu) == n
        S = set(mu)
        # E_2 = sum_t r(t)^2 where r(t)=#{(a,b) in S^2 : a+b=t}
        from collections import Counter
        rc = Counter()
        for a in mu:
            for b in mu:
                rc[(a+b) % q] += 1
        return sum(v*v for v in rc.values()), n*n
    for (q, n) in [(17,8),(97,8),(193,16),(257,16),(12289,8),(12289,16),(40961,32)]:
        if (q-1) % n != 0:
            continue
        E2, floor = e2_subgroup(q, n)
        print(f" mu_{n} in F_{q}*: E_2={E2}, |S|^2 floor={floor}, E_2/n^2={E2/floor:.3f},"
              f" E_2/n^3={E2/n**3:.4f}  (sqrt-cancel target ~ n^2 * polylog)")

def primitive_root(p):
    if p == 2: return 1
    factors = set()
    phi = p-1
    m = phi
    d = 2
    while d*d <= m:
        if m % d == 0:
            factors.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1: factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in factors):
            return g
    raise RuntimeError("no primitive root")

if __name__ == "__main__":
    main()
