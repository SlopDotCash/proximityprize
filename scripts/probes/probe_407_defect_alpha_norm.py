#!/usr/bin/env python3
"""
probe_407_defect_alpha_norm.py  --  #407: inspect an ACTUAL defect alpha; compute its TRUE norm.

The persistence probe found defect primes ABOVE the naive norm threshold (2r)^{phi/2}. That means
the naive bound |N(alpha)| <= (2r)^{phi/2} is WRONG: it assumed the coefficient L1-length in the
power basis is <= 2r, but the defect vector lives in the n-dim group-ring coords (L1<=2r THERE),
and REDUCING mod Phi_n into the phi(n)-dim power basis can BLOW UP the coefficients.

This probe extracts a concrete defect alpha at n=16, r=3 for a prime p above the naive threshold,
and computes:
   - its coefficient vector in the n-dim group-ring (L1-length = 2r exactly),
   - its reduced vector in the phi(n)-dim power basis (the TRUE algebraic-integer coords),
   - its actual norm N(alpha) (product of conjugates), and the proven divisibility p | N(alpha),
   - the CORRECT norm bound via Mahler / sum-of-squares in the power basis.
This pins down WHICH norm the lattice-counting route must control and shows the naive (2r)^{phi/2}
is the wrong object. Then we re-derive the honest threshold.

Run:  python scripts/probes/probe_407_defect_alpha_norm.py
"""
import sys, math, itertools
from collections import Counter, defaultdict

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import sympy


def reduction_table(n):
    x = sympy.symbols('x')
    Phi = sympy.Poly(sympy.cyclotomic_poly(n, x), x)
    phi_n = Phi.degree()
    Phi_coeffs = [int(c) for c in Phi.all_coeffs()][::-1]
    redtab = [[0] * phi_n for _ in range(n)]
    for k in range(phi_n): redtab[k][k] = 1
    for k in range(phi_n, n):
        prev = redtab[k - 1]
        shifted = [0] * (phi_n + 1)
        for i in range(phi_n): shifted[i + 1] += prev[i]
        top = shifted[phi_n]
        for i in range(phi_n): shifted[i] -= top * Phi_coeffs[i]
        redtab[k] = shifted[:phi_n]
    return redtab, phi_n, Phi_coeffs


def norm_of_powerbasis(vec, n):
    """N_{Q(zeta_n)/Q}(alpha) for alpha = sum vec[i] zeta^i (power basis, len phi(n)) via product
       over primitive n-th roots of unity (numerical, rounded to integer)."""
    phi_n = len(vec)
    prim = [t for t in range(1, n) if math.gcd(t, n) == 1]
    prod = 1.0
    for t in prim:
        z = complex(math.cos(2 * math.pi * t / n), math.sin(2 * math.pi * t / n))
        val = sum(vec[i] * z ** i for i in range(phi_n))
        prod *= abs(val)
    return prod  # |N(alpha)| = product of |conjugate|


def main():
    n = 16
    redtab, phi_n, Phi_coeffs = reduction_table(n)
    print(f"n={n}, phi(n)={phi_n}, Phi_n coeffs (ascending) = {Phi_coeffs}")
    # char-0 reference at r=3
    cnt0 = Counter()
    for tup in itertools.product(range(n), repeat=3):
        v = [0] * phi_n
        for t in tup:
            rk = redtab[t]
            for i in range(phi_n): v[i] += rk[i]
        cnt0[tuple(v)] += 1

    # pick a defect prime above naive threshold T=(2*3)^4=1296
    p = 4049
    assert is_prime(p) and (p - 1) % n == 0
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    zpows = [pow(z, j, p) for j in range(n)]
    print(f"prime p={p} (2^{math.log2(p):.2f}); naive norm threshold (2r)^(phi/2)=(6)^4=1296 (2^10.3)")
    print(f"  => p > threshold, yet persistence probe saw defect. Diagnosing.\n")

    # collect r=3 sums mod p, grouped by char-0 class (reduced power-basis vector):
    # a defect = two tuples in the SAME mod-p class but DIFFERENT char-0 class.
    # Equivalently: a relation tuple_x - tuple_y with group-ring coeff c (L1<=6, balanced),
    # nonzero in Z[zeta] (reduced vec != 0) but == 0 mod p.
    bymod = defaultdict(list)
    for tup in itertools.product(range(n), repeat=3):
        s = sum(zpows[t] for t in tup) % p
        v = tuple(sum(redtab[t][i] for t in tup) for i in range(phi_n))
        bymod[s].append((tup, v))

    # find a defect: same s, different v
    defect_examples = []
    for s, lst in bymod.items():
        vs = set(v for _, v in lst)
        if len(vs) > 1:
            # build a difference alpha = v1 - v2 (nonzero in Z[zeta], == 0 mod p)
            lst2 = lst
            (t1, v1) = lst2[0]
            for (t2, v2) in lst2[1:]:
                if v2 != v1:
                    alpha = tuple(v1[i] - v2[i] for i in range(phi_n))
                    if any(alpha):
                        defect_examples.append((alpha, t1, t2, s))
                        break
        if len(defect_examples) >= 5:
            break

    print(f"found {len(defect_examples)} sample defect alphas (reduced power-basis coords):")
    for alpha, t1, t2, s in defect_examples:
        # group-ring L1 length of the underlying relation: t1 multiset minus t2 multiset
        c = Counter(t1); c.subtract(Counter(t2))
        l1_group = sum(abs(v) for v in c.values())
        l1_power = sum(abs(a) for a in alpha)
        Na = norm_of_powerbasis(list(alpha), n)
        print(f"  alpha(power basis)={alpha}")
        print(f"     group-ring relation c={dict(c)}  L1(group)={l1_group} (<=2r=6)")
        print(f"     L1(power basis)={l1_power}   |N(alpha)|~{Na:.1f}  "
              f"(p divides N? {abs(round(Na) % p)==0 or abs((p-round(Na)%p))==0});  "
              f"|N|/p ~ {Na/p:.2f}")
        # correct Mahler/AM-GM bound on |N| from POWER-basis L2 length:
        l2sq_power = sum(a * a for a in alpha)
        amgm = l2sq_power ** (phi_n / 2)
        print(f"     POWER-basis L2^2={l2sq_power}  AM-GM bound |N|<=(L2^2)^(phi/2)="
              f"{amgm:.1f} (2^{math.log2(max(amgm,1)):.1f})  -- the HONEST norm bound")
    print("\nKEY: the naive (2r)^{phi/2} used L1(group)<=2r, but |N| is controlled by the POWER-basis")
    print("L2 length, which the reduction mod Phi_n can inflate. The honest threshold is")
    print("p > (max power-basis L2^2 over defect alphas)^{phi/2}. Next: bound that L2 length.")


if __name__ == "__main__":
    main()
