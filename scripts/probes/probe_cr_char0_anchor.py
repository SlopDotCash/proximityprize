#!/usr/bin/env python3
"""
probe_cr_char0_anchor.py  (issue #444, [cr-monotonicity], CHAR-0 anchor)

The large-p sweep (EXP B) shows a_r converging UPWARD as p->inf toward a clean limit.
That clean limit IS the char-0 additive energy of the literal n-th roots of unity
mu_n = {zeta^j : j=0..n-1} subset C, with A_r^{char0} = E_r^{char0} (no DC subtraction
needed in char 0: the "mean" n^{2r}/q term -> 0 as q->inf). So the honest, p-free
K_eff(n) trajectory is computed DIRECTLY from the char-0 energy.

E_r^{char0}(mu_n) = #{(a_1..a_r,b_1..b_r) in mu_n^{2r} : a_1+..+a_r = b_1+..+b_r in C}.
Since the n-th roots of unity are linearly independent over Q only up to the relation
sum of all = 0 (for n with few prime factors the integer relations are exactly the
"vanishing sums of roots of unity" classified by Conway-Jones / Lam-Leung), the count is
exactly computable for n=2^mu by working in Z[zeta_n] = Z[x]/(x^n+1 ... ) actually
Z[x]/Phi_n. We just compute sums symbolically as integer vectors in the power basis
{1, zeta, ..., zeta^{n-1}} modulo (x^n - 1)?? -> use minimal poly.

Cleanest exact route: represent zeta_n by its action, count multiplicities of r-fold
sums as elements of the CYCLOTOMIC integer ring via the reduced power basis mod Phi_n(x).
For n=2^mu, Phi_n(x) = x^{n/2}+1, degree n/2. Two r-fold sums are equal iff their
reduced coefficient vectors (length n/2) are equal. So:

  rep(j) = coefficient vector of zeta^j reduced mod x^{n/2}+1:
           if j < n/2:  e_j  (unit vector)
           else:       -e_{j-n/2}
  An r-tuple (j_1..j_r) has sum-vector = sum of rep(j_i).
  E_r = sum over sum-vectors v of (mult of v)^2,  mult = #r-tuples with that sum-vector.

This is EXACT char-0 (Lam-Leung regime), no prime, no DC artifact. K_eff = (E_r/Wick)^{1/r}.

Wick_r = (2r-1)!!*n^r. a_r = E_r/Wick_r. The Wick bound is a_r <= 1 (Lam-Leung, char-0).
"""
from fractions import Fraction
from collections import defaultdict

def rep_vectors(n):
    """For n=2^mu: zeta^j reduced mod x^{n/2}+1, as a tuple of length n/2."""
    half = n // 2
    reps = []
    for j in range(n):
        v = [0]*half
        if j < half:
            v[j] = 1
        else:
            v[j-half] = -1
        reps.append(tuple(v))
    return reps

def char0_energy(n, r):
    """E_r^{char0}(mu_n) for n a power of 2, via cyclotomic power-basis reduction."""
    reps = rep_vectors(n)
    half = n // 2
    # distribution of r-fold sum vectors
    cur = defaultdict(int)
    cur[tuple([0]*half)] = 1
    for _ in range(r):
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rv in reps:
                w = tuple(v[i]+rv[i] for i in range(half))
                nxt[w] += c
        cur = nxt
    # E_r = sum of squares of multiplicities of r-fold sums
    return sum(c*c for c in cur.values())

def dfodd(r):
    res = 1
    for k in range(1, r+1): res *= (2*k-1)
    return res

def main():
    print("ISSUE #444 [cr-monotonicity] CHAR-0 anchor: p-free K_eff(n) trajectory")
    print("E_r^{char0}(mu_n) via cyclotomic reduction mod x^{n/2}+1 (n=2^mu, Lam-Leung regime)")
    print("a_r = E_r/Wick_r,  Wick_r=(2r-1)!!*n^r,  K_eff=a_r^{1/r}.  Wick bound: a_r<=1.\n")

    ns = [4, 8, 16, 32]
    Rcap = {4: 8, 8: 8, 16: 6, 32: 4}
    tables = {}
    for n in ns:
        rows = []
        for r in range(1, Rcap[n]+1):
            E = char0_energy(n, r)
            Wick = dfodd(r)*(n**r)
            ar = Fraction(E, Wick)
            Keff = float(ar)**(1.0/r)
            rows.append((r, E, float(ar), Keff))
        tables[n] = rows
        print(f"==== n={n} ====")
        print(f"  {'r':>2} {'E_r^char0':>20} {'a_r':>10} {'K_eff':>9} {'c_r':>10}")
        for i, (r, E, ar, Keff) in enumerate(rows):
            if i+1 < len(rows):
                ar1 = rows[i+1][2]
                cr = ((1+2*r)*ar1 - ar)/(2*r)
                cr_s = f"{cr:.5f}" + (" OK" if cr <= 1+1e-12 else " >1!!")
            else:
                cr_s = "  --"
            print(f"  {r:>2} {E:>20} {ar:>10.6f} {Keff:>9.5f} {cr_s:>10}")
        print()

    print("==== CHAR-0 K_eff(n) EXTRAPOLATION (the decisive, p-free trajectory) ====")
    maxr = min(len(tables[n]) for n in ns)
    print(f"  r  | " + " ".join(f"n={n:<5}" for n in ns))
    for ri in range(maxr):
        r = ri+1
        print(f"  {r:>2} | " + " ".join(f"{tables[n][ri][3]:<7.4f}" for n in ns))

    print("\n  Verdict: at fixed r, does K_eff(n) saturate (-> bounded < 1, prize plausible)")
    print("  or grow toward 1 as n: 4->8->16->32->64?")
    # check Wick bound a_r<=1 everywhere
    viol = [(n, r) for n in ns for (r, E, ar, K) in tables[n] if ar > 1+1e-12]
    print(f"\n  Wick bound a_r<=1 (char-0): {'HOLDS everywhere' if not viol else f'VIOLATED at {viol}'}")
    # c_r<=1 everywhere
    cviol = []
    for n in ns:
        rows = tables[n]
        for i in range(len(rows)-1):
            r = rows[i][0]; ar=rows[i][2]; ar1=rows[i+1][2]
            cr = ((1+2*r)*ar1-ar)/(2*r)
            if cr > 1+1e-9: cviol.append((n,r,cr))
    print(f"  c_r<=1 (char-0): {'HOLDS everywhere' if not cviol else f'VIOLATED at {cviol}'}")

if __name__ == "__main__":
    main()
