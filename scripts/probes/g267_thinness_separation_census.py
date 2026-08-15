#!/usr/bin/env python3
"""G267: exact thinness-separation certificate for the adjacent-rank CORE covariance (#466).

Computation of record for `Frontier/_G267ThinnessSeparationCensus.lean`.

Object (the current frontier CORE surrogate, G228..G266):
  W_G(x) = #{(y,z) in G^2 : 2y - z = x},           G = order-n multiplicative subgroup of F_p^*
  R_r(x) = (dp_r ⋆ dp_{r-1})(x)                     adjacent-rank subset-sum correlation
  A_r(n,p) = p * Σ_x W_G(x) R_r(x) - (Σ W_G)(Σ R_r)   (exact integer; the CORE covariance)

G266 realised all four sign quadrants of (sgn A5, sgn A6) and left the THINNESS-POSITIVITY BIAS OPEN
(corroborated, not refuted). This probe certifies the exact FINITE separation content of that bias on
the n=8 census, exactly as formalized in the Lean file:

  * the full 90-cell n=8 census (17 <= p <= 2657, p ≡ 1 mod 8) with exact float-free signs,
  * every sign-negative cell has p-1 <= 112 (tau <= 1.75) — the hard thinness threshold,
  * every cell with p-1 >= 136 (tau >= 2.125) is (+,+) — the verified thin tail,
  * the strict separation gap (112, 136) and the >23x thin tail up to p-1 = 2656 (tau = 41.5),
  * the sign-negative set is EXACTLY {17, 73, 89, 113}.

This is a finite separation certificate, NOT a bound at production primes and NOT a proof of the
thinness repair. It sharpens G266's open bias into an exact recorded separation. Everything is
pure-Python int (no numpy, no floats).

Exits non-zero (SystemExit(1)) if any certified fact fails, so it cannot silently rot.
"""
from __future__ import annotations


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def prime_factors(n: int) -> list[int]:
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise ValueError(f"no primitive root mod {p}")


def subgroup(p: int, n: int) -> list[int]:
    root = primitive_root(p)
    z = pow(root, (p - 1) // n, p)
    out = []
    x = 1
    for _ in range(n):
        out.append(x)
        x = x * z % p
    assert x == 1 and len(set(out)) == n
    return out


def dp_hist(G: list[int], p: int, r: int) -> list[list[int]]:
    hist = [[0] * p for _ in range(r + 1)]
    hist[0][0] = 1
    used = 0
    for x in G:
        used += 1
        for k in range(min(r, used), 0, -1):
            src = hist[k - 1]
            dst = hist[k]
            for s in range(p):
                v = src[s]
                if v:
                    dst[(s + x) % p] += v
    return hist


def adj_corr(dpr: list[int], dprm1: list[int], p: int) -> list[int]:
    R = [0] * p
    for s in range(p):
        a = dpr[s]
        if a:
            for t in range(p):
                b = dprm1[t]
                if b:
                    R[(s - t) % p] += a * b
    return R


def covs(n: int, p: int) -> tuple[int, int]:
    G = subgroup(p, n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    sw = sum(W)
    hist = dp_hist(G, p, 6)
    out = []
    for r in (5, 6):
        R = adj_corr(hist[r], hist[r - 1], p)
        out.append(p * sum(W[x] * R[x] for x in range(p)) - sw * sum(R))
    return out[0], out[1]


# The exact census table hard-coded in the Lean file: (p, A5pos, A6pos).
LEAN_CENSUS = [
    (17, False, False), (41, True, True), (73, False, False), (89, False, True),
    (97, True, True), (113, False, False), (137, True, True), (193, True, True),
    (233, True, True), (241, True, True), (257, True, True), (281, True, True),
    (313, True, True), (337, True, True), (353, True, True), (401, True, True),
    (409, True, True), (433, True, True), (449, True, True), (457, True, True),
    (521, True, True), (569, True, True), (577, True, True), (593, True, True),
    (601, True, True), (617, True, True), (641, True, True), (673, True, True),
    (761, True, True), (769, True, True), (809, True, True), (857, True, True),
    (881, True, True), (929, True, True), (937, True, True), (953, True, True),
    (977, True, True), (1009, True, True), (1033, True, True), (1049, True, True),
    (1097, True, True), (1129, True, True), (1153, True, True), (1193, True, True),
    (1201, True, True), (1217, True, True), (1249, True, True), (1289, True, True),
    (1297, True, True), (1321, True, True), (1361, True, True), (1409, True, True),
    (1433, True, True), (1481, True, True), (1489, True, True), (1553, True, True),
    (1601, True, True), (1609, True, True), (1657, True, True), (1697, True, True),
    (1721, True, True), (1753, True, True), (1777, True, True), (1801, True, True),
    (1873, True, True), (1889, True, True), (1913, True, True), (1993, True, True),
    (2017, True, True), (2081, True, True), (2089, True, True), (2113, True, True),
    (2129, True, True), (2137, True, True), (2153, True, True), (2161, True, True),
    (2273, True, True), (2281, True, True), (2297, True, True), (2377, True, True),
    (2393, True, True), (2417, True, True), (2441, True, True), (2473, True, True),
    (2521, True, True), (2593, True, True), (2609, True, True), (2617, True, True),
    (2633, True, True), (2657, True, True),
]

N = 8
THRESHOLD = 112   # every negative cell has p-1 <= 112
TAIL_START = 136  # every cell with p-1 >= 136 is (+,+)


def main() -> None:
    print("=== G267 exact n=8 thinness-separation census (recomputed float-free) ===")
    # 1) Recompute the census fresh and confirm it matches the Lean table exactly.
    fresh = []
    cnt = 0
    for p in range(17, 6000):
        if not is_prime(p) or (p - 1) % N != 0:
            continue
        a5, a6 = covs(N, p)
        fresh.append((p, a5 > 0, a6 > 0))
        cnt += 1
        if cnt >= 90:
            break
    assert len(fresh) == 90, f"expected 90 cells, got {len(fresh)}"
    assert [(p, s5, s6) for (p, s5, s6) in fresh] == LEAN_CENSUS, \
        "fresh census does not match the Lean-hardcoded table"
    print(f"  census cells = {len(fresh)}; matches Lean table exactly.")

    # 2) Sign-negative set is exactly {17, 73, 89, 113}.
    neg = [(p, s5, s6) for (p, s5, s6) in fresh if not (s5 and s6)]
    neg_primes = sorted(p for (p, _, _) in neg)
    assert neg_primes == [17, 73, 89, 113], f"negative set changed: {neg_primes}"
    print(f"  sign-negative cells (exactly): {neg_primes}")

    # 3) Every negative cell has p-1 <= THRESHOLD.
    max_neg = max((p - 1) for (p, _, _) in neg)
    assert max_neg <= THRESHOLD, f"a negative cell exceeds threshold: p-1={max_neg}"
    print(f"  max (p-1) among negatives = {max_neg} (tau = {max_neg / (N * N):.3f}) "
          f"<= threshold {THRESHOLD}")

    # 4) Every cell with p-1 >= TAIL_START is (+,+).
    tail = [(p, s5, s6) for (p, s5, s6) in fresh if (p - 1) >= TAIL_START]
    assert all(s5 and s6 for (_, s5, s6) in tail), "thin tail contains a non-(+,+) cell"
    assert len(tail) >= 1, "thin tail empty"
    print(f"  thin tail (p-1 >= {TAIL_START}): {len(tail)} cells, ALL (+,+), "
          f"up to p-1 = {max(p - 1 for (p, _, _) in tail)} "
          f"(tau = {max(p - 1 for (p, _, _) in tail) / (N * N):.2f})")

    # 5) Strict separation gap (THRESHOLD, TAIL_START) and the fold factor.
    assert TAIL_START > THRESHOLD, "no separation gap"
    max_tail = max(p - 1 for (p, _, _) in tail)
    fold = max_tail / max_neg
    assert fold > 23, f"thin tail fold factor too small: {fold}"
    print(f"  separation gap = ({THRESHOLD}, {TAIL_START}); "
          f"thin tail extends to {fold:.1f}x the last sign flip.")

    print("\nVERDICT: on the n=8 census, sign-negativity is confined to p-1 <= 112 (tau <= 1.75); "
          "every cell with p-1 >= 136 is (+,+); the verified positive tail reaches tau = 41.5. "
          "Finite separation certificate (NOT a production-prime bound; thinness repair OPEN). PASS.")


if __name__ == "__main__":
    main()
