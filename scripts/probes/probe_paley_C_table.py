#!/usr/bin/env python3
"""Reproduce (and extend) the Paley-conjecture constant table of

    docs/kb/deltastar-444-paley-phase-cancellation-essay-2026-06-21.md, section 4.2

That table reports, for the Gauss periods of the order-`n` multiplicative subgroup
`H <= (Z/p)^*`,

    eta_b = sum_{h in H} e_p(b*h),        M = max_{b != 0} |eta_b|,
    C     = M / sqrt(n * log(p/n)),       C^2 = (M^2/n) / log(p/n)

at "the smallest prime = 1 mod n near n^4".  The script that produced it is not in the
tree, so this file re-derives every entry from scratch and re-checks it.

Prime-selection rule, made explicit (it reproduces all four published primes exactly):
the least prime p = 1 (mod n) with p >= n^4.

Two independent invariants are asserted at every n, so a silently wrong subgroup or a
silently wrong transform cannot pass:

  * Parseval:            sum_{b=0}^{p-1} |eta_b|^2 = p*n
  * fourth-moment law:   sum_{b != 0} |eta_b|^4 = p*E2 - n^4  with  E2 = 3n^2 - 3n

The second is the essay's own section-4.1 claim, so the run also re-checks that.

Usage:
    python3 scripts/probes/probe_paley_C_table.py            # n = 8..128
    python3 scripts/probes/probe_paley_C_table.py 256        # a single n
"""

import math
import sys
import time

import numpy as np
from sympy import isprime, primitive_root

# Published table, section 4.2:  n -> (p, M, C, C^2)
PUBLISHED = {
    8: (4129, 7.5582, 1.0692, 1.1432),
    16: (65537, 13.8375, 1.1995, 1.4388),
    32: (1048609, 22.9834, 1.2600, 1.5877),
    64: (16777601, 38.5286, 1.3635, 1.8590),
}

CHUNK = 1 << 22


def rule_prime(n: int) -> int:
    """Least prime p = 1 (mod n) with p >= n**4."""
    base = n**4
    k = -(-(base - 1) // n)  # ceil((base-1)/n)
    while True:
        p = 1 + k * n
        if p >= base and isprime(p):
            return p
        k += 1


def subgroup(p: int, n: int) -> list[int]:
    """The unique order-`n` subgroup of (Z/p)^*."""
    g = primitive_root(p)
    assert g is not None, f"no primitive root for {p}"
    h = pow(int(g), (p - 1) // n, p)
    out, x = [], 1
    for _ in range(n):
        out.append(x)
        x = x * h % p
    assert len(set(out)) == n, "generator did not have order n"
    return out


def _mulmod(b: np.ndarray, h: int, p: int) -> np.ndarray:
    """(b*h) mod p without int64 overflow.

    Splitting `h` at 16 bits keeps every intermediate under 2^49 even when p ~ 2^32,
    where the naive product b*h would reach ~2^63 and silently wrap.
    """
    hi, lo = divmod(h, 1 << 16)
    return (((b * hi) % p) * (1 << 16) + b * lo) % p


def scan(p: int, n: int):
    """Return (M, S2, S4) over b = 1..p-1.

    |eta_b| = |eta_{p-b}| because the subgroup indicator is real, so the scan runs over
    the lower half and doubles the power sums.
    """
    H = subgroup(p, n)
    half = (p - 1) // 2
    M = 0.0
    s2 = 0.0
    s4 = 0.0
    for start in range(1, half + 1, CHUNK):
        b = np.arange(start, min(start + CHUNK, half + 1), dtype=np.int64)
        re = np.zeros(len(b))
        im = np.zeros(len(b))
        for h in H:
            ang = _mulmod(b, h, p).astype(np.float64) * (2 * math.pi / p)
            re += np.cos(ang)
            im += np.sin(ang)
        sq = re * re + im * im
        M = max(M, float(np.sqrt(sq.max())))
        s2 += float(sq.sum())
        s4 += float((sq * sq).sum())
    return M, 2.0 * s2, 2.0 * s4


def run(n: int) -> None:
    p = rule_prime(n)
    t0 = time.time()
    M, s2, s4 = scan(p, n)
    C = M / math.sqrt(n * math.log(p / n))

    # Parseval: sum over ALL b, so add back the b=0 term |eta_0|^2 = n^2.
    parseval = s2 + n * n
    assert abs(parseval / (p * n) - 1) < 1e-9, f"Parseval failed: {parseval} vs {p*n}"

    # Fourth moment: sum_{b != 0} |eta_b|^4 = p*E2 - n^4, E2 = 3n^2 - 3n.
    e2 = (s4 + n**4) / p
    assert abs(e2 - (3 * n * n - 3 * n)) < 1e-3 * n * n, f"E2 = {e2}, want {3*n*n-3*n}"

    line = f"{n:>5} {p:>12} {M:>10.4f} {C:>8.4f} {C*C:>8.4f}"
    if n in PUBLISHED:
        _, mp, cp, c2p = PUBLISHED[n]
        ok = abs(M - mp) < 5e-3 and abs(C - cp) < 5e-4 and abs(C * C - c2p) < 5e-4
        line += f"   | published {mp:>9.4f} {cp:>7.4f} {c2p:>7.4f}  {'MATCH' if ok else 'MISMATCH'}"
    else:
        line += "   | new"
    print(line + f"   [{time.time()-t0:.0f}s]", flush=True)


def main() -> None:
    ns = [int(a) for a in sys.argv[1:]] or [8, 16, 32, 64, 128]
    print("Paley constant table: p = least prime = 1 (mod n) with p >= n^4")
    print(f"{'n':>5} {'p':>12} {'M':>10} {'C':>8} {'C^2':>8}")
    for n in ns:
        run(n)
    print("\nParseval and the E2 = 3n^2-3n fourth-moment law hold at every n above.")


if __name__ == "__main__":
    main()
