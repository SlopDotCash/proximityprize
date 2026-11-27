#!/usr/bin/env python3
"""Independent verification probe for Milestone 5:
QuarterPivotDomainIndependentBarrier.lean.

Verifies:
1. The zero-search 4-head (2n + 2)-bad-scalar construction at quarter-rate
   Johnson sign pivot e = 2d + 3 = n/2 + 1 (t = 2d + 1, k = d + 1, n = 4d + 4)
   over finite fields of multiple sizes (n = 16, 32, 64, 128).
2. Literal smooth-subgroup instantiation H = mu_16 < F_1009 (d = 3, k = 4,
   e = 9, t = 7), including explicit separating (a, b) and brute-force check
   over all 1009 scalars confirming >= 34 > 32 = 2n bad scalars AND zero
   correlated agreement at t = 7.
3. Production-scale instantiation n = 2^30, k = 2^28, d = 2^28 - 1,
   e = 536,870,913 over the certified 159-bit prime
   Q = 730750818869487914369817427303088068110372044801:
   - complete factorization of Q - 1 into primes <= 357283,
   - Lucas primality certificate with primitive root g = 3,
   - Q // 2^128 == 2^31 == 2n, 2^30 | (Q - 1), (d - 1) | (Q - 1),
   - distinctness of 1, 2^(d-1), 3^(d-1) mod Q,
   - (2n + 2) choose 2 <= Q and 1/2^128 < (2n + 2)/Q,
   - strict inequality 536,870,913 / 2^30 < 1 - sqrt(2^28 / 2^30 - 1/2^30)
     (and < 1 - sqrt(1/4) = 1/2? Wait: Johnson radius is 1 - sqrt(rho) = 1/2!
      Check finite Johnson radius J(k) = 1 - sqrt((k-1)/n)!).
"""

import math
import sys


def poly_eval_g(x, d, q):
    return (pow(x, d - 1, q) - 1) % q


def verify_small_instance(d, q, omega, u0, v0, domain=None, check_bruteforce=False):
    n = 4 * (d + 1)
    k = d + 1
    t = 2 * d + 1
    e = 2 * d + 3
    assert n - t == e
    assert pow(omega, d - 1, q) == 1
    # Verify exact order d - 1
    seen = {pow(omega, j, q) for j in range(d - 1)}
    assert len(seen) == d - 1

    r0 = pow(u0, d - 1, q)
    s0 = pow(v0, d - 1, q)
    assert len({1, r0, s0}) == 3, "1, r0, s0 not distinct"
    lam = ((s0 - 1) * pow((s0 - r0) % q, -1, q)) % q
    assert lam not in (0, 1)

    B12 = [pow(omega, j, q) for j in range(d - 1)]
    B13 = [(u0 * pow(omega, j, q)) % q for j in range(d - 1)]
    B23 = [(v0 * pow(omega, j, q)) % q for j in range(d - 1)]
    U = set(B12) | set(B13) | set(B23)
    assert len(U) == 3 * (d - 1)

    if domain is None:
        rem = [x for x in range(q) if x not in U][: d + 7]
        assert len(rem) == d + 7
    else:
        assert len(domain) == n and len(set(domain)) == n
        assert U.issubset(set(domain)), "B12 U B13 U B23 not subset of domain"
        rem = [x for x in domain if x not in U]
        assert len(rem) == d + 7

    E1 = rem[0:2]
    E2 = rem[2:4]
    E3 = rem[4:6]
    Brem = rem[6 : 6 + d + 1]
    H = B12 + B13 + B23 + E1 + E2 + E3 + Brem
    assert len(H) == n and len(set(H)) == n

    def g12(x):
        return (pow(x, d - 1, q) - 1) % q

    def g13(x):
        return (lam * (pow(x, d - 1, q) - r0)) % q

    # Heads h in {0, 1, 2, 3}: (p_h, q_h, r_h)
    def head_eval(h, x):
        if h == 0:
            return (0, 0, 0)
        elif h == 1:
            g = g12(x)
            return (0, (x * g) % q, g)
        elif h == 2:
            g = g13(x)
            return (0, (x * g) % q, g)
        else:
            g = g12(x)
            return (g, (lam * x * g) % q, (lam * g) % q)

    # Received words (u, v, w) on H
    parts = (
        [("B12", x, 0) for x in B12]
        + [("B13", x, 0) for x in B13]
        + [("B23", x, 1) for x in B23]
        + [("E1", x, 0) for x in E1]
        + [("E2", x, 1) for x in E2]
        + [("E3", x, 2) for x in E3]
        + [("Brem", x, 3) for x in Brem]
    )
    rec = {x: head_eval(owner, x) for _, x, owner in parts}

    # Verify cores
    cores = {
        0: set(B12) | set(B13) | set(E1),
        1: set(B12) | set(B23) | set(E2),
        2: set(B13) | set(B23) | set(E3),
        3: set(B12) | set(Brem),
    }
    for h in range(4):
        assert len(cores[h]) == 2 * d
        for x in cores[h]:
            assert head_eval(h, x) == rec[x], f"Core mismatch h={h}, x={x}"

    # Collect 8d + 10 fresh events
    fresh_map = {
        "B12": [2],
        "B13": [1, 3],
        "B23": [0, 3],
        "E1": [1, 3],
        "E2": [0, 3],
        "E3": [0, 3],
        "Brem": [0, 1, 2],
    }
    keys = []
    events = []
    for tag, x, _ in parts:
        ux, vx, wx = rec[x]
        for h in fresh_map[tag]:
            ph, qh, rh = head_eval(h, x)
            denom = (rh - wx) % q
            assert denom != 0, f"Zero denom at {tag}, x={x}, h={h}"
            k0 = ((ux - ph) * pow(denom, -1, q)) % q
            k1 = ((vx - qh) * pow(denom, -1, q)) % q
            assert k1 == (-x) % q, f"key1 mismatch: {k1} != {(-x) % q}"
            keys.append((k0, k1))
            events.append((h, x))

    expected_count = 8 * d + 10
    assert len(events) == expected_count == 2 * n + 2
    assert len(set(keys)) == expected_count, (
        f"Duplicate keys! {len(set(keys))} < {expected_count}"
    )

    if check_bruteforce:
        # Find explicit separating (a, b) with a = 1
        sep_b = None
        for b in range(q):
            vals = {(k0 + b * k1) % q for k0, k1 in keys}
            if len(vals) == expected_count:
                sep_b = b
                break
        assert sep_b is not None, "No separating (1, b) found!"
        a, b = 1, sep_b
        U_word = [(a * rec[x][0] + b * rec[x][1]) % q for x in H]
        W_word = [rec[x][2] for x in H]

        # Verify each event produces a valid RS(H, k) codeword agreeing on >= t = 2d+1 sites
        bad_scalars = set()
        for (h, x_fresh), (k0, k1) in zip(events, keys):
            gamma = (a * k0 + b * k1) % q
            # Polynomial (a*p_h + b*q_h) + gamma * r_h has degree <= d < k
            agree = 0
            for idx, x in enumerate(H):
                ph, qh, rh = head_eval(h, x)
                cval = (a * ph + b * qh + gamma * rh) % q
                if cval == (U_word[idx] + gamma * W_word[idx]) % q:
                    agree += 1
            assert agree >= t, f"Expected >= {t} agreements, got {agree}"
            bad_scalars.add(gamma)
        assert len(bad_scalars) == expected_count

        # Verify NO correlated agreement at t = 2d+1 (brute-force over all C(n, k) bases?
        # Even simpler: check every pair of degree <= d polynomials matching U_word and W_word
        # simultaneously on >= k sites! Any correlated pair on >= t = 7 sites agrees on >= 4 sites
        # of W_word, so both polynomials are uniquely determined by any k-subset of their common
        # agreement set!)
        from itertools import combinations

        def lagrange_eval(pts, vals, x_eval):
            res = 0
            for i in range(len(pts)):
                num, den = 1, 1
                for j in range(len(pts)):
                    if i != j:
                        num = (num * (x_eval - pts[j])) % q
                        den = (den * (pts[i] - pts[j])) % q
                res = (res + vals[i] * num * pow(den, -1, q)) % q
            return res

        max_corr = 0
        for sub in combinations(range(n), k):
            pts = [H[i] for i in sub]
            u_sub = [U_word[i] for i in sub]
            w_sub = [W_word[i] for i in sub]
            both = 0
            for i in range(n):
                if (
                    lagrange_eval(pts, u_sub, H[i]) == U_word[i]
                    and lagrange_eval(pts, w_sub, H[i]) == W_word[i]
                ):
                    both += 1
            if both > max_corr:
                max_corr = both
        assert max_corr == 2 * d < t, f"Unexpected correlated agreement {max_corr} >= {t}"
        print(
            f"  [BRUTEFORCE PASS] d={d}, n={n}, k={k}, e={e}, t={t}, q={q}: "
            f"sep=(1,{sep_b}), |B|>={len(bad_scalars)}={2*n+2} > 2n={2*n}, "
            f"max_correlated_agree={max_corr} < t={t}"
        )
    else:
        print(
            f"  [PASS] d={d}, n={n}, k={k}, e={e}, t={t}, q={q}: "
            f"{expected_count} distinct keys (= 2n + 2)"
        )


def verify_production():
    d = 2**28 - 1
    n = 2**30
    k = 2**28
    e = 536_870_913
    t = n - e
    assert n == 4 * (d + 1)
    assert k == d + 1
    assert e == 2 * d + 3
    assert t == 2 * d + 1

    Q = 730750818869487914369817427303088068110372044801
    # Exact factorization check
    expected_Q_minus_1 = (2**92) * (5**2) * 7 * 13 * 17 * 73 * 557 * 262657 * 357283
    assert Q - 1 == expected_Q_minus_1
    primes = [2, 5, 7, 13, 17, 73, 557, 262657, 357283]

    # Deterministic trial-division primality of every prime factor of Q - 1
    for p in primes:
        assert p >= 2
        for div in range(2, math.isqrt(p) + 1):
            assert p % div != 0, f"{p} divisible by {div}"

    # Lucas primality certificate for Q with witness g = 3
    g = 3
    assert pow(g, Q - 1, Q) == 1
    for p in primes:
        assert pow(g, (Q - 1) // p, Q) != 1

    # Prize-shape & divisibility checks
    assert Q // (2**128) == 2**31 == 2 * n
    assert (Q - 1) % (2**30) == 0
    assert (Q - 1) % (d - 1) == 0

    # Root of unity omega of exact order d - 1
    omega = pow(g, (Q - 1) // (d - 1), Q)
    assert pow(omega, d - 1, Q) == 1
    for p in [2, 7, 73, 262657]:
        assert pow(omega, (d - 1) // p, Q) != 1

    # Distinctness of 1, 2^(d-1), 3^(d-1) mod Q
    r0 = pow(2, d - 1, Q)
    s0 = pow(3, d - 1, Q)
    assert len({1, r0, s0}) == 3

    # Field size & security threshold checks
    S_card = 8 * d + 10
    assert S_card == 2 * n + 2 == 2_147_483_650
    assert math.comb(S_card, 2) <= Q
    assert S_card * (2**128) > Q  # 1/2^128 < (2n + 2) / Q

    # Finite Johnson radius comparison at k = 2^28, n = 2^30:
    # J(k) = 1 - sqrt((k - 1) / n). Check e / n < J(k) <=> (n - e)^2 > n * (k - 1)
    assert (n - e) ** 2 > n * (k - 1)
    assert (n - (e + 1)) ** 2 < n * (k - 1)
    print(
        f"  [PRODUCTION PASS] Q={Q}\n"
        f"    Q-1 = 2^92 * 5^2 * 7 * 13 * 17 * 73 * 557 * 262657 * 357283\n"
        f"    Q // 2^128 = {Q // 2**128} == 2^31 == 2n\n"
        f"    |S| = {S_card} > Q // 2^128, choose(|S|, 2) <= Q: {math.comb(S_card, 2) <= Q}\n"
        f"    Pivot cell check: (n - e)^2 - n*(k-1) = {(n - e)**2 - n*(k - 1)} > 0,\n"
        f"                      (n - e - 1)^2 - n*(k-1) = {(n - e - 1)**2 - n*(k - 1)} < 0"
    )


def main():
    print("=== Milestone 5 Probe: Quarter-Rate Johnson Pivot Domain-Independent Barrier ===")
    # 1. Literal smooth subgroup H = mu_16 < F_1009 (d = 3, k = 4, n = 16, e = 9, t = 7)
    q = 1009
    # Find element of order 16 in F_1009 (1008 = 16 * 63; primitive root 11 -> zeta = 11^63 mod 1009)
    zeta = pow(11, 63, q)
    assert pow(zeta, 16, q) == 1 and pow(zeta, 8, q) != 1
    mu16 = [pow(zeta, i, q) for i in range(16)]
    omega = pow(zeta, 8, q)  # = -1 mod 1009, order 2 = d - 1
    verify_small_instance(
        d=3, q=q, omega=omega, u0=zeta, v0=pow(zeta, 2, q), domain=mu16, check_bruteforce=True
    )

    # 2. General domains at d = 7 (n = 32), d = 15 (n = 64), d = 31 (n = 128)
    for d in [7, 15, 31]:
        m = d - 1
        target = math.comb(8 * d + 10, 2)
        c = (target + m - 1) // m
        while True:
            q = c * m + 1
            if all(q % p != 0 for p in range(2, math.isqrt(q) + 1)):
                break
            c += 1
        # find generator of order m
        omega = None
        for g in range(2, q):
            cand = pow(g, (q - 1) // m, q)
            if pow(cand, m, q) == 1 and len({pow(cand, j, q) for j in range(m)}) == m:
                omega = cand
                break
        # find u0, v0 with 1, u0^m, v0^m distinct
        u0 = next(x for x in range(2, q) if pow(x, m, q) != 1)
        v0 = next(x for x in range(2, q) if pow(x, m, q) not in (1, pow(u0, m, q)))
        verify_small_instance(d=d, q=q, omega=omega, u0=u0, v0=v0, check_bruteforce=False)

    # 3. Production scale n = 2^30, e = 536,870,913
    verify_production()
    print("=== ALL CHECKS PASSED ===")


if __name__ == "__main__":
    main()
