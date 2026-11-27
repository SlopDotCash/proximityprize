#!/usr/bin/env python3
"""Exact integer interval-arithmetic norm bounds for Q(zeta_64)^+ dihedral pullbacks on mu_64.

Uses ONLY exact arbitrary-precision integer arithmetic (zero floating point).
Certifies that for any disjoint size-7 trace supports A, B and any two distinct
points x, y in the trace image (excluding fixed points 0, 32 in the even case),
the algebraic norm |N_{Q(zeta_64)^+/Q}(1 - rho)| satisfies:
  - Odd reflection (c = zeta_64, 32 nodes, all pairs up to Gal): < 2^136 < p1 < p2
  - Even reflection (c = 1, 33 nodes, all interior pairs x,y in {1..31} up to Gal): < 2^156 < p1 < p2.
"""
from __future__ import annotations

from functools import cache
from math import isqrt
import numpy as np

PRIME_1 = (1 << 158) + 192 * (1 << 30) + 1
PRIME_2 = (1 << 159) + 13 * (1 << 30) + 1

SCALE_COS = 1 << 80
LOG_SCALE = 1024
EXP_SHIFT = 32


@cache
def twice_cos(n: int, t: int) -> tuple[int, int]:
    """Closed exact integer enclosure [lo, hi] of SCALE_COS * 2*cos(2*pi*t/n) for dyadic n."""
    t %= n
    if n == 2:
        v = (-2 if t else 2) * SCALE_COS
        return v, v
    if 4 * t in (n, 3 * n):
        return 0, 0
    lo, hi = twice_cos(n // 2, t % (n // 2))
    lo_s = isqrt(max(0, (2 * SCALE_COS + lo) * SCALE_COS))
    hi_s = isqrt((2 * SCALE_COS + hi) * SCALE_COS) + 1
    return (-hi_s, -lo_s) if n < 4 * t < 3 * n else (lo_s, hi_s)


def diff_enclosure(is_odd: bool, k: int, x: int, z: int) -> tuple[int, int]:
    """Closed positive integer enclosure [lo, hi] of SCALE_COS * |sigma_k(s_x - s_z)|."""
    if is_odd:
        ax, bx = twice_cos(128, k * (2 * x - 1))
        az, bz = twice_cos(128, k * (2 * z - 1))
    else:
        ax, bx = twice_cos(64, k * x)
        az, bz = twice_cos(64, k * z)
    d_lo = ax - bz
    d_hi = bx - az
    if d_lo > 0:
        return d_lo, d_hi
    if d_hi < 0:
        return -d_hi, -d_lo
    raise ArithmeticError(f"Difference enclosure straddles zero: {(is_odd, k, x, z)}")


def exact_ceil_log2_scaled(val: int, scale: int, s: int) -> int:
    """Smallest integer L such that (val / scale)^s <= 2^L (exact integers)."""
    assert val > 0 and scale > 0
    p = val ** s
    q = scale ** s
    if p >= q:
        L = max(0, p.bit_length() - q.bit_length())
        while (q << L) < p:
            L += 1
        while L > 0 and (q << (L - 1)) >= p:
            L -= 1
        assert p <= (q << L) and (L == 0 or p > (q << (L - 1)))
        return L
    m = max(0, q.bit_length() - p.bit_length())
    while (p << m) > q:
        m -= 1
    while (p << (m + 1)) <= q:
        m += 1
    assert (p << m) <= q and (p << (m + 1)) > q
    return -m


def exact_floor_log2_scaled(val: int, scale: int, s: int) -> int:
    """Largest integer L such that 2^L <= (val / scale)^s."""
    return -exact_ceil_log2_scaled(scale, val, s)


def build_pow2_frac_hi() -> list[int]:
    """Exact integer ceiling of 2^(EXP_SHIFT + r / LOG_SCALE) for r in 0..LOG_SCALE-1."""
    table = [0] * LOG_SCALE
    for r in range(LOG_SCALE):
        target = 1 << (r + EXP_SHIFT * LOG_SCALE)
        lo_c, hi_c = 1 << EXP_SHIFT, 1 << (EXP_SHIFT + 1)
        while lo_c < hi_c:
            mid = (lo_c + hi_c) // 2
            if mid ** LOG_SCALE >= target:
                hi_c = mid
            else:
                lo_c = mid + 1
        assert lo_c ** LOG_SCALE >= target
        table[r] = lo_c
    return table


def precompute_diff_logs(is_odd: bool) -> tuple[np.ndarray, np.ndarray]:
    """Precompute exact outward-rounded log2 enclosures for |sigma_{2e+1}(s_i - s_j)|."""
    start = 1 if is_odd else 0
    n_sites = 32 if is_odd else 33
    hi_tbl = np.zeros((16, start + n_sites, start + n_sites), dtype=np.int64)
    lo_tbl = np.zeros((16, start + n_sites, start + n_sites), dtype=np.int64)
    for e in range(16):
        k = 2 * e + 1
        for i in range(start, start + n_sites):
            for j in range(i + 1, start + n_sites):
                lo_d, hi_d = diff_enclosure(is_odd, k, i, j)
                hi_l = exact_ceil_log2_scaled(hi_d, SCALE_COS, LOG_SCALE)
                lo_l = exact_floor_log2_scaled(lo_d, SCALE_COS, LOG_SCALE)
                hi_tbl[e, i, j] = hi_tbl[e, j, i] = hi_l
                lo_tbl[e, i, j] = lo_tbl[e, j, i] = lo_l
    return lo_tbl, hi_tbl


def exact_bound_pair(
    is_odd: bool,
    x: int,
    y: int,
    lo_tbl: np.ndarray,
    hi_tbl: np.ndarray,
    pow2_hi: list[int],
    bits8: np.ndarray,
    d: int = 7,
) -> int:
    """Rigorous exact integer upper bound on |N_{Q(zeta_64)^+/Q}(1 - rho)|."""
    start = 1 if is_odd else 0
    n_sites = 32 if is_odd else 33
    sites = [j for j in range(start, start + n_sites) if j != x and j != y]
    m = len(sites)
    # Since lo_y <= |sy - sz| <= hi_y and lo_x <= |sx - sz| <= hi_x:
    # log2(|sy - sz| / |sx - sz|) <= hi_y - lo_x  and  >= lo_y - hi_x.
    hi_log = hi_tbl[:, y, sites] - lo_tbl[:, x, sites]  # (16, m)
    lo_log = lo_tbl[:, y, sites] - hi_tbl[:, x, sites]  # (16, m)

    hi_lo8 = bits8 @ hi_log[:8]
    hi_hi8 = bits8 @ hi_log[8:]
    lo_lo8 = bits8 @ lo_log[:8]
    lo_hi8 = bits8 @ lo_log[8:]

    all_exps = np.empty(65536, dtype=np.int64)
    for h in range(256):
        H = hi_lo8 + hi_hi8[h]
        L = lo_lo8 + lo_hi8[h]
        top_d = np.partition(H, m - d, axis=1)[:, m - d:].sum(axis=1)
        bot_d = np.partition(L, d - 1, axis=1)[:, :d].sum(axis=1)
        all_exps[h * 256:(h + 1) * 256] = top_d - bot_d

    max_e = int(all_exps.max())
    base_bits = (max_e // LOG_SCALE) - 40
    total_scaled = 0
    for e in all_exps.tolist():
        diff_e = e - base_bits * LOG_SCALE
        if diff_e <= 0:
            total_scaled += 1 << EXP_SHIFT
        else:
            q, r = divmod(diff_e, LOG_SCALE)
            total_scaled += pow2_hi[r] << q

    shift = base_bits - EXP_SHIFT
    if shift >= 0:
        return total_scaled << shift
    s = -shift
    return (total_scaled + (1 << s) - 1) >> s


def main() -> None:
    assert (PRIME_1 - 1) % 128 == 0 and (PRIME_2 - 1) % 128 == 0
    assert (1 << 136) < (1 << 156) < PRIME_1 < PRIME_2

    pow2_hi = build_pow2_frac_hi()
    masks8 = np.arange(256, dtype=np.int64)[:, None]
    bits8 = ((masks8 >> np.arange(8, dtype=np.int64)) & 1).astype(np.int64)

    # 1. Odd reflection: Gal(Q(zeta_128)^+/Q) acts transitively on {1..32}, so x=1 is WLOG.
    lo_odd, hi_odd = precompute_diff_logs(True)
    worst_odd = 0
    worst_odd_y = -1
    for y in range(2, 33):
        b = exact_bound_pair(True, 1, y, lo_odd, hi_odd, pow2_hi, bits8, d=7)
        if b > worst_odd:
            worst_odd, worst_odd_y = b, y
    assert worst_odd < (1 << 136) < PRIME_1 < PRIME_2
    print(
        f"ODD REFLECTION (all 31 Galois-rep pairs, x=1, y=2..32, d=7): "
        f"worst at y={worst_odd_y}, bit_length={worst_odd.bit_length()}, "
        f"certified < 2^136 < p1 < p2",
        flush=True,
    )

    # 2. Even reflection: Gal(Q(zeta_64)^+/Q) acts transitively on each v2-class of {1..31};
    # every unordered pair {x, y} subset {1..31} maps to x in {1, 2, 4, 8} with y > x.
    lo_even, hi_even = precompute_diff_logs(False)
    worst_even = 0
    worst_even_pair = (-1, -1)
    even_pairs = [(x, y) for x in (1, 2, 4, 8) for y in range(x + 1, 32)]
    assert len(even_pairs) == 109
    for x, y in even_pairs:
        b = exact_bound_pair(False, x, y, lo_even, hi_even, pow2_hi, bits8, d=7)
        if b > worst_even:
            worst_even, worst_even_pair = b, (x, y)
    assert worst_even < (1 << 156) < PRIME_1 < PRIME_2
    print(
        f"EVEN REFLECTION (all {len(even_pairs)} Galois-rep interior pairs in {{1..31}}, d=7): "
        f"worst at {worst_even_pair}, bit_length={worst_even.bit_length()}, "
        f"certified < 2^156 < p1 < p2",
        flush=True,
    )


if __name__ == "__main__":
    main()
