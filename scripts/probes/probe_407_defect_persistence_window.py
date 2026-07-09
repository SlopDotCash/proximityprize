#!/usr/bin/env python3
"""
probe_407_defect_persistence_window.py  --  #407: does the defect VANISH above the norm threshold?

The norm/Mahler bound says: alpha in P\{0}, L1-length <= 2r  =>  p <= |N(alpha)| <= (2r)^{phi(n)/2}.
So for p > (2r)^{phi(n)/2}, defect(r) = 0 EXACTLY (this is the only proven mechanism).
The wall: in the prize regime p ~ n^beta, beta in [4,5], and r ~ ln p ~ beta ln n, the threshold
(2r)^{phi(n)/2} = (2 beta ln n)^{(n/2)} >> p, so the bound is VACUOUS and cannot certify defect=0.

This probe asks the EMPIRICAL question the route turns on:
  At fixed depth r, sweep ALL primes p = 1 mod n (non-dyadic) in a window straddling the norm
  threshold T(r) = (2r)^{phi(n)/2}. Does defect(r,p) really drop to 0 for ALL p > T(r) (norm bound),
  AND does it ALSO drop to 0 well before T(r) (i.e. is the norm bound LOOSE -- could a counting
  argument give a much smaller effective threshold)?

If the EFFECTIVE defect-vanishing threshold T_eff(r) is MUCH smaller than T(r)=(2r)^{phi/2}, say
T_eff(r) = poly(r) * n^c for a small constant c, THEN the prize regime p ~ n^beta would clear it at
deep r and the route would WORK. If T_eff(r) tracks (2r)^{phi/2} (exponential in n), the route walls.

Run:  python scripts/probes/probe_407_defect_persistence_window.py
"""
import sys, math, itertools
from collections import Counter

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import sympy


def subgroup_mod_p(p, n):
    g = primitive_root(p); z = pow(g, (p - 1) // n, p)
    return [pow(z, j, p) for j in range(n)]


def Er_char0_coeffs(n, r):
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
    cnt = Counter()
    for tup in itertools.product(range(n), repeat=r):
        v = [0] * phi_n
        for t in tup:
            rk = redtab[t]
            for i in range(phi_n): v[i] += rk[i]
        cnt[tuple(v)] += 1
    return sum(c * c for c in cnt.values())


def Er_mod_p_enum(p, H, n, r):
    cnt = Counter()
    for tup in itertools.product(H, repeat=r):
        cnt[sum(tup) % p] += 1
    return sum(c * c for c in cnt.values())


def primes_1mod_n_in(n, lo, hi):
    out = []
    c = ((lo + n - 1) // n) * n + 1
    while c <= hi:
        if is_prime(c) and odd_part((c - 1) // n) > 1:
            out.append(c)
        c += n
    return out


def main():
    print("=" * 84)
    print(" #407 DEFECT PERSISTENCE: defect(r,p) across the norm threshold T(r)=(2r)^(phi(n)/2)")
    print("=" * 84)
    for n in (8, 16):
        phi_n = int(sympy.totient(n))
        E0 = {r: Er_char0_coeffs(n, r) for r in range(2, 4)}
        print(f"\n n={n}  phi(n)={phi_n}.   prize regime: p >= n^2 = {n*n} (n<=sqrt(p)).")
        for r in (2, 3):
            T = (2 * r) ** (phi_n // 2) if phi_n % 2 == 0 else None
            Tlog = math.log2(T) if T else float('nan')
            print(f"\n  -- r={r}: char-0 E_r^(0)={E0[r]}.  norm threshold T=(2r)^(phi/2)="
                  f"{T} (~2^{Tlog:.1f}).  n^2=2^{2*math.log2(n):.1f}")
            # sweep window from a bit below n^2 up to ~ 4*T
            lo = max(2 * n, n * n // 4)
            hi = min(int(4 * T) if T else 10**7, 6_000_000 if n ** r < 50_000 else 200_000)
            primes = primes_1mod_n_in(n, lo, hi)
            last_defect_p = None
            first_clean_after = None
            rows = []
            for p in primes:
                if p ** 0 and n ** r > 4_000_000:  # guard enumeration cost
                    break
                H = subgroup_mod_p(p, n)
                Er = Er_mod_p_enum(p, H, n, r)
                d = Er - E0[r]
                rows.append((p, d))
                if d > 0:
                    last_defect_p = p
            # report: largest p with defect, vs T and vs n^2
            if last_defect_p:
                print(f"     largest defect prime in window = {last_defect_p} "
                      f"(~2^{math.log2(last_defect_p):.2f});  T~2^{Tlog:.1f};  "
                      f"ratio last_defect/T = {last_defect_p/T:.3f}; "
                      f"last_defect/n^2 = {last_defect_p/(n*n):.2f}")
            else:
                print(f"     NO defect prime in window [{lo},{hi}] -- defect already 0 at p>={lo}")
            # show the tail rows near the transition
            tail = [(p, d) for p, d in rows if d > 0][-3:] + [(p, d) for p, d in rows if d == 0][:3]
            for p, d in sorted(set(tail)):
                flag = "DEFECT" if d > 0 else "clean "
                print(f"        p={p:>8} (2^{math.log2(p):5.2f})  defect={d:>12}  {flag}"
                      f"  {'[> T]' if T and p>T else '[<=T]'}  {'[>=n^2]' if p>=n*n else '[<n^2]'}")
    print("\nCONCLUSION KEY:")
    print("  If 'largest defect prime' tracks T=(2r)^(phi/2) (exponential in n=phi): norm bound is")
    print("  TIGHT, route walls -- defect persists up to the vacuous threshold in the prize regime.")
    print("  If it is << T and ~ poly(r)*n^O(1): the norm bound is LOOSE, a counting argument could")
    print("  give a small effective threshold and the route could work.")


if __name__ == "__main__":
    main()
