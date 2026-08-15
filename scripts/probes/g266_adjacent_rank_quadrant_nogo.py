#!/usr/bin/env python3
"""G266: adjacent-rank CORE covariance realises all four quadrants — no cross-rank / thinness sign lock.

Computation of record for `Frontier/_G266AdjacentRankQuadrantNoGo.lean`.

Object (the current frontier CORE surrogate, G228..G265):
  W_G(x) = #{(y,z) in G^2 : 2y - z = x},           G = order-n multiplicative subgroup of F_p^*
  R_r(x) = (dp_r ⋆ dp_{r-1})(x)
         = #{(A,B) : A ⊆ G, |A|=r, B ⊆ G, |B|=r-1, (Σ A) - (Σ B) = x},   dp_k[x]=#{k-subsets summing to x}
  A_r(n,p) = p * Σ_x W_G(x) R_r(x) - (Σ_x W_G(x))(Σ_x R_r(x))       (exact integer; the CORE covariance)

Certifies:
  * the exact integer witnesses hard-coded in the Lean file (recomputed float-free), and
  * the four-quadrant census: all of {++,+-,-+,--} occur over genuine cells n in {8,16,32},
    INCLUDING the rare (-+); hence no cross-rank sign implication A6>0=>A5>0, no adjacent-rank forced
    sign, and no thinness-forced sign. A (+,+) bias grows with thinness tau=(p-1)/n^2 but is not a bound.

Everything is pure-Python int (no numpy, no floats).
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
    """hist[k][x] = #{k-subsets of G with sum = x mod p}, exact int."""
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
    """R(x) = Σ_s dpr[s] · dprm1[(s - x) mod p]."""
    R = [0] * p
    for s in range(p):
        a = dpr[s]
        if a:
            for t in range(p):
                b = dprm1[t]
                if b:
                    R[(s - t) % p] += a * b
    return R


def cov(n: int, p: int, r: int) -> int:
    G = subgroup(p, n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    hist = dp_hist(G, p, r)
    R = adj_corr(hist[r], hist[r - 1], p)
    return p * sum(W[x] * R[x] for x in range(p)) - sum(W) * sum(R)


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


def main() -> None:
    print("=== G266 exact witnesses (recomputed float-free) ===")
    expect = {
        (8, 89): (-256, 40, "(-,+)"),
        (8, 113): (-13128, -7240, "(-,-)"),
        (8, 2969): (4357008, 1894816, "(+,+) thin tau=46.4"),
    }
    ok = True
    for (n, p), (e5, e6, tag) in expect.items():
        a5, a6 = covs(n, p)
        match = (a5 == e5 and a6 == e6)
        ok = ok and match
        print(f"  n={n} p={p}: A5={a5} A6={a6}  expect=({e5},{e6}) {tag}  MATCH={match}")
    assert ok, "witness mismatch"

    print("\n=== four-quadrant census over genuine cells ===")
    quads = {"++": 0, "+-": 0, "-+": 0, "--": 0}
    minusplus = []
    total = 0
    for n in (8, 16, 32):
        cnt = 0
        for p in range(17, 2000):
            if not is_prime(p) or (p - 1) % n != 0:
                continue
            try:
                a5, a6 = covs(n, p)
            except Exception:
                continue
            total += 1
            cnt += 1
            key = ("+" if a5 > 0 else "-") + ("+" if a6 > 0 else "-")
            quads[key] += 1
            if a5 < 0 and a6 > 0:
                minusplus.append((n, p, a5, a6))
            if cnt >= 25:
                break
    print(f"  cells={total}  quadrants={quads}")
    print(f"  (-+) witnesses: {minusplus[:5]}")
    assert all(quads[k] > 0 for k in ("++", "+-", "-+", "--")), \
        f"not all four quadrants realised: {quads}"
    assert len(minusplus) >= 1, "(-+) not realised in census range"

    # Thinness-bias record (NOT a refutation of the thinness repair; it is corroborated).
    # At n=8, all negatives are thick (tau<=1.8); thin cells are (+,+). Record, do not overclaim.
    thin_neg = []
    for n in (8,):
        cnt = 0
        for p in range(17, 4000):
            if not is_prime(p) or (p - 1) % n != 0:
                continue
            try:
                a5, a6 = covs(n, p)
            except Exception:
                continue
            cnt += 1
            tau = (p - 1) / (n * n)
            if a5 < 0 or a6 < 0:
                thin_neg.append((tau, p))
            if cnt >= 60:
                break
    max_neg_tau = max((t for t, _ in thin_neg), default=0.0)
    print(f"  n=8 negative cells: {len(thin_neg)}, max tau among them = {max_neg_tau:.2f} "
          f"(thinness-positivity bias: OPEN, not refuted)")

    print("\nVERDICT: all four quadrants realised (incl. (-+)); no cross-rank sign lock, "
          "no adjacent-rank forced sign at either rank. Thinness bias recorded, left OPEN. PASS.")


if __name__ == "__main__":
    main()
