#!/usr/bin/env python3
"""
probe_466_bilinear_dft_chain.py -- LANE R3 (#466): adversarial verification of the
round-1 P6 side-discovery chain

    bilinear (3,3) + sqrt(p)-DFT finisher:
      leg1 (di Benedetto 2003.06165 eq 5.2-5.6):  |X| >= H^6 D^6 / (c L^2 T3 D1^2),
            every x in X has |T(x)| > H D1,  D1 >= D^3/4     (ONE dyadic pigeonhole)
      leg2 (NO second pigeonhole): |X| (H D1)^3 <= sum_{x in X} |T(x)|^3
            <= sqrt(T3) * sqrt(p |X|)      (CS over w + Parseval completion, exact)
      splice:  H^12 D^6 D1^4 <= c' L^2 p T3^2  ==>  H^12 D^18 <= c'' L^2 p T3^2
      good prime T3 <= 15 n^3  ==>  M = H D <= 15^{1/9} H^{2/3} p^{1/18 + o(1)}
      beta=4:  M <= n^{8/9+o(1)}; saving law (6-beta)/18; dies at beta=6;
      dominates the landed trilinear 23/24 (saving (7-beta)/72) for beta < 17/3.

Every intermediate inequality above that is a THEOREM (not a good-prime input) is
verified EXACTLY on real F_p data below, at the worst-case a (the argmax coset),
with the actual dyadic pigeonhole executed.  Constants are tracked, not waved.

Regime discipline: p prime, p = 1 mod n, p > n^4 (beta >= 4 at the small end),
n != p-1, two primes per n where feasible.
"""

import math, cmath, sys
from fractions import Fraction as F
from collections import defaultdict

LINE = "-" * 78

# ---------------------------------------------------------------- primes / mu_n

def is_prime(m):
    if m < 2:
        return False
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if m % a == 0:
            return m == a
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def primes_1modn(n, count=2):
    out, p = [], n ** 4 + 1
    while len(out) < count:
        if p % n == 1 and is_prime(p) and p - 1 != n:
            out.append(p)
        p += n
    return out


def mun(n, p):
    for cand in range(2, p):
        h = pow(cand, (p - 1) // n, p)
        if h != 1 and pow(h, n // 2, p) != 1:
            g = h
            break
    H, x = [], 1
    for _ in range(n):
        H.append(x)
        x = x * g % p
    assert len(set(H)) == n
    return H


def find_generator(p):
    # factor p-1 crudely (p-1 = n * m, small enough here)
    q = p - 1
    fac = set()
    d = 2
    while d * d <= q:
        while q % d == 0:
            fac.add(d)
            q //= d
        d += 1
    if q > 1:
        fac.add(q)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fac):
            return g
    raise RuntimeError


# ---------------------------------------------------------------- the chain

def run_case(n, p):
    H = mun(n, p)
    Hs = set(H)
    tau = 2 * math.pi / p

    def esum(a):
        return abs(sum(cmath.exp(1j * tau * (a * x % p)) for x in H))

    # worst a over dilation-coset representatives g^j, j = 0..m-1
    g = find_generator(p)
    m = (p - 1) // n
    best_a, M = None, -1.0
    a = 1
    for _ in range(m):
        v = esum(a)
        if v > M:
            M, best_a = v, a
        a = a * g % p
    D = M / n  # Delta

    # J3 rep function (3-fold), T3, and T(w) on supp J3
    J2 = defaultdict(int)
    for x in H:
        for y in H:
            J2[(x + y) % p] += 1
    J3 = defaultdict(int)
    for s, v in J2.items():
        for z in H:
            J3[(s + z) % p] += v
    T3 = sum(v * v for v in J3.values())
    T3_char0 = 15 * n ** 3 - 45 * n * n + 40 * n
    a0 = best_a
    Tw = {w: abs(sum(cmath.exp(1j * tau * (a0 * w % p * y % p)) for y in H))
          for w in J3}

    # eq 5.2 (theorem): n^4 D^3 <= sum_w J3(w) |T(w)|
    lhs52 = n ** 4 * D ** 3
    rhs52 = sum(J3[w] * Tw[w] for w in J3)
    ok52 = lhs52 <= rhs52 * (1 + 1e-9)

    # dyadic pigeonhole on |T(w)|/n over triples (weight J3(w)); cut at D^3/2
    cut = n * D ** 3 / 2
    levels = defaultdict(lambda: [0, 0.0, []])  # j -> [count(G1), contribution, ws]
    tail = 0.0
    for w, jw in J3.items():
        t = Tw[w]
        if t < cut:
            tail += jw * t
            continue
        j = 0
        while t <= n * 2.0 ** (-(j + 1)):
            j += 1
        lv = levels[j]
        lv[0] += jw
        lv[1] += jw * t
        lv[2].append(w)
    L = len(levels)
    ok_tail = tail <= rhs52 / 2 + 1e-9 or tail < lhs52 / 2 + 1e-9
    # popular level = max contribution
    jstar = max(levels, key=lambda j: levels[j][1])
    G1, contrib, Xws = levels[jstar]
    D1 = 2.0 ** (-(jstar + 1))          # lower edge / n
    X = len(Xws)

    # pigeonhole guarantees (theorems given the cut):
    ok_lvl = contrib >= (lhs52 / 2) / max(L, 1) * (1 - 1e-9) or contrib >= lhs52 / (2 * L) * (1 - 1e-9)
    ok_D1 = D1 >= D ** 3 / 4 * (1 - 1e-9)
    ok_G1 = G1 >= n ** 3 * D ** 3 / (4 * L * D1) * (1 - 1e-9)
    ok_edge = all(Tw[w] > n * D1 * (1 - 1e-12) for w in Xws)

    # leg1 CS (theorem): G1^2 <= X * T3
    ok_cs1 = G1 * G1 <= X * T3

    # leg2 CS + Parseval completion (theorem):
    #   sum_{x in X} |T(x)|^3 <= sqrt(T3) * sqrt(p * X)
    s3 = sum(Tw[w] ** 3 for w in Xws)
    rhs_leg2 = math.sqrt(T3) * math.sqrt(p * X)
    ok_leg2 = s3 <= rhs_leg2 * (1 + 1e-9)
    lhs_leg2 = X * (n * D1) ** 3
    ok_leg2b = lhs_leg2 <= s3 * (1 + 1e-9)

    # spliced master (with tracked constants): n^12 D^6 D1^4 <= 16 L^2 p T3^2
    lhsM = n ** 12 * D ** 6 * D1 ** 4
    rhsM = 16 * L * L * p * T3 * T3
    okM = lhsM <= rhsM * (1 + 1e-9)
    # collapsed: n^12 D^18 <= 4096 L^2 p T3^2
    lhsC = n ** 12 * D ** 18
    rhsC = 4096 * L * L * p * T3 * T3
    okC = lhsC <= rhsC * (1 + 1e-9)

    # end bound: M <= 15^{1/9} (4096 * 225/225... constants) -- report clean ratio
    clean = 15 ** (1 / 9.0) * n ** (2 / 3.0) * p ** (1 / 18.0)
    const_full = (4096 * L * L * 225) ** (1 / 18.0)

    print(f"  n={n} p={p} (beta={math.log(p)/math.log(n):.3f})  worst a={a0}  "
          f"M={M:.3f}  Delta={D:.5f}")
    print(f"    T3={T3} char0={T3_char0} good-prime match={T3 == T3_char0}")
    print(f"    eq5.2  n^4 D^3 = {lhs52:.1f} <= sum J3|T| = {rhs52:.1f}   OK={ok52}")
    print(f"    pigeonhole: L={L} levels above cut, tail<=half OK={ok_tail}; "
          f"popular j*={jstar}  D1={D1:.5f}  |G1|={G1}  |X|={X}")
    print(f"      D1 >= D^3/4 ({D**3/4:.6f})            OK={ok_D1}")
    print(f"      contrib >= n^4 D^3/(2L)               OK={ok_lvl}")
    print(f"      |G1| >= n^3 D^3/(4 L D1) = {n**3*D**3/(4*L*D1):.1f}   OK={ok_G1}")
    print(f"      every x in X: |T(x)| > n D1           OK={ok_edge}")
    print(f"    leg1 CS: |G1|^2 = {G1*G1} <= |X| T3 = {X*T3}   OK={ok_cs1}")
    print(f"    leg2:   |X|(nD1)^3 = {lhs_leg2:.1f} <= sum|T|^3 = {s3:.1f} "
          f"<= sqrt(p T3 |X|) = {rhs_leg2:.1f}   OK={ok_leg2b and ok_leg2}")
    print(f"    MASTER  n^12 D^6 D1^4 = {lhsM:.3e} <= 16 L^2 p T3^2 = {rhsM:.3e}  "
          f"OK={okM}  (slack {rhsM/lhsM:.1e})")
    print(f"    COLLAPSED n^12 D^18 = {lhsC:.3e} <= 4096 L^2 p T3^2 = {rhsC:.3e}  "
          f"OK={okC}  (slack {rhsC/lhsC:.1e})")
    print(f"    end bound: M={M:.2f} vs clean 15^(1/9) n^(2/3) p^(1/18) = {clean:.2f} "
          f"(x const {const_full:.2f} tracked)   M<=clean*const OK={M <= clean*const_full}")
    allok = all([ok52, ok_tail, ok_D1, ok_lvl, ok_G1, ok_edge, ok_cs1, ok_leg2,
                 ok_leg2b, okM, okC, M <= clean * const_full])
    print(f"    CASE ALL-THEOREM-STEPS OK: {allok}")
    return allok, (T3 == T3_char0)


# ---------------------------------------------------------------- exponent laws

def exponent_table():
    print(LINE)
    print("EXPONENT LAWS (exact rationals)")
    print(LINE)
    ok = True
    for beta in [F(3), F(4), F(9, 2), F(5), F(11, 2), F(17, 3), F(6), F(13, 2), F(7)]:
        bi = F(6 - beta, 18) if beta < 6 else F(0) if beta == 6 else None
        bi_raw = (6 - beta) / 18
        tri_raw = (7 - beta) / 72
        theta_bi = 1 - bi_raw
        winner = ("bilinear" if bi_raw > tri_raw else
                  "tie" if bi_raw == tri_raw else "trilinear")
        print(f"  beta={str(beta):>5s}: bilinear saving={str(bi_raw):>7s} "
              f"theta={str(theta_bi):>7s}  trilinear saving={str(tri_raw):>7s}  "
              f"winner={winner}")
    checks = [
        ((6 - F(4)) / 18 == F(1, 9), "saving(4) = 1/9"),
        (1 - (6 - F(4)) / 18 == F(8, 9), "theta(4) = 8/9"),
        ((6 - F(6)) / 18 == 0, "dies at beta=6"),
        ((6 - F(4)) / 18 > (7 - F(4)) / 72, "dominates trilinear 23/24 at beta=4"),
        (1 - (7 - F(4)) / 72 == F(23, 24), "trilinear theta(4) = 23/24 (landed)"),
        # crossover: bilinear > trilinear iff 4(6-b) > 7-b iff b < 17/3
        (all(((6 - b) / 18 > (7 - b) / 72) == (b < F(17, 3))
             for b in [F(4), F(5), F(11, 2), F(17, 3), F(23, 4), F(6)]),
         "crossover exactly at beta = 17/3"),
        (F(2, 3) + F(4, 18) == F(8, 9), "2/3 + beta/18 at beta=4 = 8/9"),
    ]
    for val, name in checks:
        print(f"  CHECK {name}: {val}")
        ok = ok and val
    return ok


# ---------------------------------------------------------------- main

print(LINE)
print("CHAIN VERIFICATION ON REAL F_p DATA (worst-coset a, actual pigeonhole)")
print(LINE)
all_ok, good_prime = True, True
for n in [8, 16]:
    for p in primes_1modn(n, 2):
        ok, gp = run_case(n, p)
        all_ok = all_ok and ok
        good_prime = good_prime and gp
# one larger case, single prime (cost)
for p in primes_1modn(32, 1):
    ok, gp = run_case(32, p)
    all_ok = all_ok and ok
    good_prime = good_prime and gp

print()
exp_ok = exponent_table()

print()
print(LINE)
print("VERDICT")
print(LINE)
print(f"  All THEOREM-steps of the chain hold exactly on data: {all_ok}")
print(f"  Good-prime T3 = char-0 value at all tested (n,p):    {good_prime}")
print(f"  Exponent laws ((6-beta)/18, 8/9 at beta=4, die at 6,")
print(f"    dominate 23/24 for beta<17/3):                     {exp_ok}")
print(f"  CHAIN STATUS: {'CONFIRMED' if all_ok and exp_ok else 'REFUTED -- see failing step'}")
print("""  Honesty: good-prime-conditional (T3 <= 15 n^3 fails on D3(n), which contains
  prize-regime primes at n=32 -- _AvJ_UnconditionalBeat.lean); the 8/9 exponent is
  the HIGH side of the BGK wall (prize needs 1/2); NOT prize closure; and by
  deltaStar_determination_all_or_nothing a fixed power law cannot move delta*.""")
