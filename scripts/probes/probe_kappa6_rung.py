#!/usr/bin/env python3
"""
probe_kappa6_rung.py  (Issue #444, route [cumulant] / r=3 rung)

GOAL. The DC-subtracted Wick bound at r=3 is the first *clean-regime* moment rung past
r<=2.  We want to (a) pin the EXACT closed forms of the additive energies E_1,E_2,E_3 of a
PROPER subgroup mu_n <= F_p^* with 4 | n, (b) verify the cumulant-from-moment identity that
relates the 6th cumulant kappa6 of X=|eta_b|^2 to E_1,E_2,E_3, (c) check the central claim
        A_3  =  kappa6 - 45 n^2 + 15 n^3        (4|n symmetric)
        kappa6 <= 45 n^2     (the rung inequality)
and (d) report the margin kappa6 / n^2 across n=16..128.

DEFINITIONS (everything EXACT integer / Fraction; b ranges over b != 0 mod p, i.e. the
DC-subtracted "house" distribution, m = (p-1)/n distinct periods each with multiplicity n).

  eta_b   = sum_{x in mu_n} e_p(b x)                (Gauss period)
  X_b     = |eta_b|^2  (real, >= 0)
  Raw DC-subtracted power sums:
     S_r := sum_{b != 0} X_b^r = sum_{b!=0} |eta_b|^{2r} = p * E_r - n^{2r}
  (the n^{2r} removes the b=0 term eta_0 = n; this is the DC subtraction.)

  E_r = #{(x_1..x_r,y_1..y_r) in mu_n^{2r} : sum x_i = sum y_j}   (r-fold additive energy, char p)

  A_r := S_r / p  =  E_r - n^{2r}/p   (the per-period DC-subtracted r-th moment, the object the
        Wick bound bounds; A_r ~ E_r for p >> n^{2r}).

We compute kappa6 as the classical 3rd cumulant of the *raw additive-energy* moment sequence
mu_r := E_r (the natural "moment" attached to the subgroup, char-0 anchor), i.e.
     kappa1 = mu1
     kappa2 = mu2 - mu1^2
     kappa3 = mu3 - 3 mu1 mu2 + 2 mu1^3
and we ALSO compute kappa6 := kappa3 of the sequence (E_1,E_2,E_3) -- i.e. the "6th cumulant
of eta" = 3rd cumulant of X.  We test which normalization makes the task identity hold.
"""

from fractions import Fraction
from sympy import primerange, isprime

def subgroup_energies_charp(p, n):
    """Exact char-p additive energies E_1,E_2,E_3 of the order-n subgroup mu_n <= F_p^*.
    Requires n | (p-1).  Returns (E1,E2,E3) as ints (counts of tuples in mu_n^{2r} summing equal),
    arithmetic done in Z/pZ."""
    assert (p - 1) % n == 0
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    mu = []
    x = 1
    for _ in range(n):
        mu.append(x)
        x = (x * step) % p
    assert len(set(mu)) == n
    # E1 = #{(a,b): a=b} = n
    E1 = n
    # E2 = #{(a,b,c,d): a+b=c+d mod p}
    # count via sumset multiplicities of pairwise sums
    from collections import Counter
    sums2 = Counter()
    for a in mu:
        for b in mu:
            sums2[(a + b) % p] += 1
    E2 = sum(v * v for v in sums2.values())
    # E3 = #{(a,b,c, d,e,f): a+b+c = d+e+f}
    sums3 = Counter()
    for a in mu:
        for b in mu:
            ab = (a + b) % p
            for c in mu:
                sums3[(ab + c) % p] += 1
    E3 = sum(v * v for v in sums3.values())
    return E1, E2, E3

def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    factors = set()
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")

def classical_kappa3(m1, m2, m3):
    """3rd classical cumulant from first 3 raw moments."""
    return m3 - 3 * m1 * m2 + 2 * m1**3

def charzero_E(n):
    """Exact char-0 (unit-circle mu_n) additive energies, n even (4|n covered):
       E1 = n
       E2 = 3 n^2 - 3 n          (n even; negation-closed)
       E3 = 15 n^3 - 45 n^2 + 40 n   (claimed)
    """
    return n, 3*n*n - 3*n, 15*n**3 - 45*n**2 + 40*n

def find_prime(n, mult_lo):
    """smallest prime p = n*k+1 with k >= mult_lo, ensuring p >> n^3 (proper subgroup)."""
    k = mult_lo
    while True:
        p = n * k + 1
        if isprime(p):
            return p
        k += 1

print("="*108)
print("PART A — char-0 closed forms E_3 = 15n^3-45n^2+40n, and the cumulant identity")
print("="*108)
print(f"{'n':>5} {'E1':>6} {'E2(c0)':>10} {'E3(c0)':>14} {'kappa6=k3(E)':>16} {'45n^2':>12} {'k6/n^2':>9} {'k6<=45n^2?':>11}")
for n in [4,8,12,16,20,24,28,32,48,64,96,128]:
    E1,E2,E3 = charzero_E(n)
    k6 = classical_kappa3(E1,E2,E3)
    print(f"{n:>5} {E1:>6} {E2:>10} {E3:>14} {k6:>16} {45*n*n:>12} {k6/n**2:>9.4f} {str(k6 <= 45*n*n):>11}")

print()
print("Test task identity  A_3 = kappa6 - 45 n^2 + 15 n^3, with A_3 = E_3 (char-0 limit p->inf):")
print(f"{'n':>5} {'E3':>14} {'k6-45n^2+15n^3':>16} {'match?':>8}")
for n in [4,8,16,32,64,128]:
    E1,E2,E3 = charzero_E(n)
    k6 = classical_kappa3(E1,E2,E3)
    rhs = k6 - 45*n*n + 15*n**3
    print(f"{n:>5} {E3:>14} {rhs:>16} {str(E3==rhs):>8}")

print()
print("="*108)
print("PART B — char-p EXACT (proper subgroup mu_n, p >> n^3): does E_3 keep the char-0 form?")
print("="*108)
print(f"{'n':>5} {'p':>10} {'mult m':>8} {'E2(cp)':>10} {'E2(c0)':>10} {'E3(cp)':>14} {'E3(c0)':>14} {'E3 clean?':>10}")
for n in [4,8,12,16,20,24,28,32]:
    # ensure p >> n^3 : pick multiplier so p > 50 n^3
    mult_lo = max(2, (50*n**3)//n + 1)
    p = find_prime(n, mult_lo)
    if p > 6_000_000 and n >= 28:
        # cap cost; still p >> n^3
        pass
    try:
        E1,E2,E3 = subgroup_energies_charp(p, n)
    except Exception as e:
        print(f"{n:>5} {p:>10}  ERR {e}")
        continue
    _,E2c0,E3c0 = charzero_E(n)
    m = (p-1)//n
    print(f"{n:>5} {p:>10} {m:>8} {E2:>10} {E2c0:>10} {E3:>14} {E3c0:>14} {str(E3==E3c0):>10}")

print()
print("="*108)
print("PART C — the rung inequality kappa6 <= 45 n^2 with EXACT char-p energies + margin")
print("="*108)
print(f"{'n':>5} {'p':>10} {'kappa6(cp)':>14} {'45n^2':>12} {'k6/n^2':>9} {'<=45?':>7}")
maxratio = 0.0
for n in [4,8,12,16,20,24,28,32]:
    mult_lo = max(2, (50*n**3)//n + 1)
    p = find_prime(n, mult_lo)
    try:
        E1,E2,E3 = subgroup_energies_charp(p, n)
    except Exception as e:
        continue
    k6 = classical_kappa3(E1,E2,E3)
    ratio = k6 / n**2
    maxratio = max(maxratio, ratio)
    print(f"{n:>5} {p:>10} {k6:>14} {45*n*n:>12} {ratio:>9.4f} {str(k6 <= 45*n*n):>7}")
print(f"\nmax kappa6/n^2 over swept proper subgroups = {maxratio:.4f}   (45 = the slack ceiling)")
