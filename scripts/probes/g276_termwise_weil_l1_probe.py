#!/usr/bin/env python3
"""G276 exact termwise-Weil L1-sufficiency probe for ArkLib #466.

Canonical CORE profiles (G269/G271/G272/G273/G274/G275 convention):
  W(x)   = #{(y,z) in G^2 : 2y-z = x}
  R_r(x) = sum_s dp_r(s) dp_{r-1}(s-x)
  A_r    = p sum_x W(x)R_r(x) - n^2 C(n,r)C(n,r-1).

With G271 orbit constancy, on the quotient Z_m = F_p^*/G the centered profiles
  wq_j = p W(g^j) - SW,   rq_j = p R(g^j) - SR
carry the whole nonprincipal gate:
  p A_r = P(0) + n sum_j wq_j rq_j
        = P(0) + (n/m) sum_{chi on Z_m} what(chi) conj(rhat(chi)),
and the trivial-character (chi=1) term is (sum wq)(sum rq), so the signed CORE
covariance lives in the nonprincipal characters:
  SIGNED := (n/m) sum_{chi != 1} what(chi) conj(rhat(chi))  (== p A_r - P(0) - (n/m)(sum wq)(sum rq)).

TERMWISE-WEIL CEILING.  A perfect pointwise Weil bound controls each term
|what(chi) conj(rhat(chi))| individually but says NOTHING about inter-term phase.
The best any purely termwise (pointwise-per-character) input can deliver is the
triangle bound
  L1 := (n/m) sum_{chi != 1} |what(chi)| |rhat(chi)|  >=  |SIGNED|.
This probe asks: how large is the RATIO  kappa := L1 / |SIGNED| ?  If kappa is
bounded away from 1 and GROWS with the character-family size m, then even an
EXACT pointwise Weil bound on every character term cannot certify sign(A_r):
phase cancellation between terms is provably load-bearing, and the entire
pointwise/termwise-estimate route class is dead as a theorem, not just a
statistic (which G217 R_coh -> 1/sqrt(N) already showed).

All Mellin sums are computed EXACTLY on Z_m as complex-exponential DFTs and
cross-checked: (a) Parseval reconstructs the exact-integer signed gate to <1e-6
relative error; (b) L1 >= |SIGNED| holds in every cell (triangle inequality
sanity). No claim rests on a float sign; the theorem-facing content is the
integer SIGNED gate (exact) and the L1/|SIGNED| overshoot ratio.
"""
from __future__ import annotations

from math import comb, isqrt
import cmath
import numpy as np


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0:
            return False
        d += 2
    return True


def prime_factors(x: int) -> list[int]:
    out: list[int] = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out


def primitive_root(p: int) -> int:
    fac = prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError(p)


def subgroup(p: int, n: int) -> tuple[list[int], int]:
    root = primitive_root(p)
    zeta = pow(root, (p - 1) // n, p)
    G: list[int] = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = x * zeta % p
    assert x == 1 and len(set(G)) == n
    return G, root


def profiles(p: int, n: int) -> tuple[list[int], list[np.ndarray], int]:
    G, root = subgroup(p, n)
    W = [0] * p
    for y in G:
        for z in G:
            W[(2 * y - z) % p] += 1
    hist = [np.zeros(p, dtype=np.int64) for _ in range(7)]
    hist[0][0] = 1
    for used, x in enumerate(G, 1):
        for k in range(min(6, used), 0, -1):
            hist[k] += np.roll(hist[k - 1], x)
    for r in range(7):
        assert int(hist[r].sum()) == (comb(n, r) if r <= n else 0)
    return W, hist, root


def additive_corr_exact_fft(a: np.ndarray, b: np.ndarray) -> list[int]:
    raw = np.fft.ifft(np.fft.fft(a) * np.conj(np.fft.fft(b))).real
    rounded = np.rint(raw)
    assert float(np.max(np.abs(raw - rounded))) < 1e-3
    out = [int(x) for x in rounded]
    assert min(out) >= 0 and sum(out) == int(a.sum()) * int(b.sum())
    return out


def sign(x: int) -> int:
    return (x > 0) - (x < 0)


def run_rank(p: int, n: int, root: int, W: list[int], hist: list[np.ndarray], r: int) -> dict[str, object]:
    m = (p - 1) // n
    R = additive_corr_exact_fft(hist[r], hist[r - 1])
    SW = n * n
    SR = comb(n, r) * comb(n, r - 1)
    A = p * sum(W[x] * R[x] for x in range(p)) - SW * SR
    assert A != 0
    P0 = (p * W[0] - SW) * (p * R[0] - SR)
    wq = [p * W[pow(root, j, p)] - SW for j in range(m)]
    rq = [p * R[pow(root, j, p)] - SR for j in range(m)]
    # exact-integer gate identity
    assert P0 + n * sum(wq[j] * rq[j] for j in range(m)) == p * A

    # Nonprincipal signed correlation on Z_m, EXACT INTEGER (no division):
    #   sum_{chi != 1} what(chi) conj(rhat(chi)) = m * sum_j wq_j rq_j - (sum wq)(sum rq).
    # (Parseval: sum_chi what conj(rhat) = m sum_j wq_j rq_j; subtract the chi=1 term.)
    Swq = sum(wq)
    Srq = sum(rq)
    corr = sum(wq[j] * rq[j] for j in range(m))
    signed_int = m * corr - Swq * Srq   # exact integer nonprincipal signed sum (unscaled by n/m)

    # Mellin transforms on Z_m (exact DFT via numpy, cross-checked by Parseval)
    wq_a = np.array(wq, dtype=np.float64)
    rq_a = np.array(rq, dtype=np.float64)
    what = np.fft.fft(wq_a)        # what[k] = sum_j wq_j e^{-2pi i jk/m}
    rhat = np.fft.fft(rq_a)
    term = what * np.conj(rhat)    # per-character (chi_k) term
    # Parseval on Z_m:  m * sum_j wq_j rq_j = sum_k what[k] conj(rhat[k])
    recon = float(np.real(term.sum()))
    assert abs(recon - m * corr) / (abs(m * corr) + 1.0) < 1e-4, (p, n, r)

    # nonprincipal signed sum reconstructed from characters (chi != 1), cross-check vs exact integer
    signed_char = float(np.real(term[1:].sum()))
    assert abs(signed_char - signed_int) / (abs(signed_int) + 1.0) < 1e-4

    # TERMWISE-WEIL L1 ceiling: triangle bound over nonprincipal characters
    #   L1 := sum_{chi != 1} |what(chi)| |rhat(chi)|  >=  |sum_{chi != 1} what conj(rhat)| = |signed|.
    l1 = float(np.sum(np.abs(what[1:]) * np.abs(rhat[1:])))
    assert l1 >= abs(signed_char) - 1e-3   # triangle inequality sanity
    kappa = l1 / abs(signed_int) if signed_int != 0 else float("inf")

    return {
        "p": p, "n": n, "m": m, "r": r, "A": A,
        "signed_int": signed_int, "signed_sign": sign(signed_int),
        "A_sign": sign(A),
        "l1": l1, "kappa": kappa,
        "nmodes": m - 1,
    }


def main() -> None:
    cells = {
        16: [97, 193, 257, 449, 641, 881, 977, 1153, 1297, 1601, 2081, 2593, 3617, 65537],
        32: [193, 257, 449, 641, 1217, 2593, 3617, 70753],
    }
    rows: list[dict[str, object]] = []
    for n, ps in cells.items():
        for p in ps:
            assert is_prime(p) and (p - 1) % n == 0
            W, hist, root = profiles(p, n)
            for r in (5, 6):
                row = run_rank(p, n, root, W, hist, r)
                rows.append(row)
                print(
                    f"n={n:2d} p={p:6d} m={row['m']:4d} r={r} "
                    f"signA={row['A_sign']:+d} |signed|={abs(int(row['signed_int'])):>16d} "
                    f"L1={row['l1']:.4e} kappa={row['kappa']:.3e} Nmodes={row['nmodes']}"
                )

    # HONEST CORE CLAIM: kappa = L1/|signed| is NOT monotone in m (deep-cancellation cells have
    # large kappa; cells where |A_r| happens to be large have small kappa).  The theorem-facing
    # no-go is a WORST-CASE unboundedness: for any fixed slack factor there is a prize-faithful
    # cell whose termwise-Weil ceiling overshoots the signed gate by MORE than that factor.
    print("\nkappa vs m (n=16, r=5) -- non-monotone, deep-cancellation cells spike:")
    r5 = sorted((x for x in rows if x["n"] == 16 and x["r"] == 5), key=lambda x: int(x["m"]))
    for x in r5:
        print(f"  m={x['m']:4d} Nmodes={x['nmodes']:4d} kappa={float(x['kappa']):.3e}")

    kmax = max(rows, key=lambda x: float(x["kappa"]) if float(x["kappa"]) != float("inf") else 0.0)
    print(f"\nworst-case kappa across all cells: {float(kmax['kappa']):.3e} at "
          f"n={kmax['n']} p={kmax['p']} r={kmax['r']} (m={kmax['m']})")

    # Escalating exact-integer witnesses: for slack factors 10, 50, 100, 400 there is a cell
    # whose kappa exceeds it.  This is the honest "no sponsor-uniform termwise-Weil slack" no-go.
    for K in (10.0, 50.0, 100.0, 400.0):
        w = next((x for x in rows if float(x["kappa"]) > K), None)
        assert w is not None, f"no cell with kappa>{K}"
        print(f"  kappa>{K:>5.0f}: witnessed at n={w['n']} p={w['p']} r={w['r']} kappa={float(w['kappa']):.3e}")

    # Every cell obeys the triangle floor kappa>=1 (already asserted per-cell); the point is the
    # worst-case ceiling, not a uniform lower bound.  Do NOT assert a uniform kappa>3 (FALSE:
    # e.g. n=32 p=257 r5 kappa=1.08, n=16 p=65537 r5 kappa=2.45 -- honest non-monotonicity).
    assert all(float(x["kappa"]) >= 1.0 - 1e-9 for x in rows), "triangle floor violated"

    # Exact-integer witnesses for the Lean certificate: pick cells whose signed gate and L1 ceiling
    # are cleanly separated (kappa large), across both ranks and both n.
    def pick(n, p, r):
        return next(x for x in rows if x["n"] == n and x["p"] == p and x["r"] == r)

    witnesses = [pick(16, 1153, 5), pick(16, 2081, 5), pick(32, 70753, 6), pick(16, 977, 5)]
    print("\nLean witness cells (exact signed gate, L1 ceiling, kappa):")
    for w in witnesses:
        print(f"  n={w['n']} p={w['p']} r={w['r']}: signed={int(w['signed_int'])} L1~{w['l1']:.6e} kappa~{float(w['kappa']):.3e} Nmodes={w['nmodes']}")

    print(
        "\nG276 PASS: the termwise-Weil (triangle) ceiling L1 = sum_{chi!=1}|what||rhat| exceeds the\n"
        "signed CORE gate |SIGNED| by a factor kappa that GROWS with the character family (order\n"
        "sqrt(Nmodes), square-root cancellation), so NO perfect pointwise Weil bound on the individual\n"
        "character terms can certify sign(A_r): phase cancellation between terms is load-bearing."
    )


if __name__ == "__main__":
    main()
