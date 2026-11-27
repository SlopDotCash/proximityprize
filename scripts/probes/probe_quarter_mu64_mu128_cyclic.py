#!/usr/bin/env python3
"""Exact verifiers for QuarterMu64Mu128CyclicExclusion.lean:
1. Exhausts all 111 rotation+Galois orbits of 7-subsets of mu_16 (orbit sum C(16,7) = 11,440)
   for mu_64 Case 2B at BOTH MOD = 101 and MOD = 103, certifying 0 non-antipodal solutions.
2. Certifies pure-integer outward-rounded Q(zeta_64)^+ norm bound < 2^151 < p1 < p2 for ALL
   109 Galois-representative interior pairs of the anti-invariant deg-15 reflection on mu_64.
3. Compiles and runs probe_quarter_mu64_anti_deg15.cpp across all 47,251 orbits at MOD = 101, 103
   (orbit sum C(31,6) = 736,281), certifying 0 consistent systems.
"""
from __future__ import annotations

from functools import cache
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import subprocess
import tempfile
import numpy as np

PRIME_1 = (1 << 158) + 192 * (1 << 30) + 1
PRIME_2 = (1 << 159) + 13 * (1 << 30) + 1
SCALE_COS = 1 << 80
LOG_SCALE = 1024
EXP_SHIFT = 32


def verify_mu64_case2B() -> None:
    n = 64
    exps = np.zeros((n, 16), dtype=np.int64)
    for d in range(1, n):
        mult = d & -d
        u = d // mult
        step = n // mult
        for j in range(mult):
            r = (u + j * step) % n
            exps[d, (min(r, n - r) - 1) // 2] += 1

    orbits = (
        [(4 * k,) for k in range(16)]
        + [(4 * k + 2, 4 * k + 34) for k in range(8)]
        + [(2 * k + 1, 2 * k + 17, 2 * k + 33, 2 * k + 49) for k in range(8)]
    )
    weights = np.array([len(o) for o in orbits], dtype=np.int64)
    exp_orb = np.zeros((64, 32, 16), dtype=np.int64)
    for x in range(0, 64, 4):
        for j, orb in enumerate(orbits):
            if x in orb:
                continue
            for y in orb:
                exp_orb[x, j] += exps[(x - y) % 64]

    seen: set[tuple[int, ...]] = set()
    reps: list[tuple[int, ...]] = []
    orbit_sum = 0
    for rest in combinations(range(1, 16), 6):
        c_set = (0,) + rest
        imgs = {
            tuple(sorted(((c - b) * k) % 16 for c in c_set))
            for b in range(16)
            for k in range(1, 16, 2)
        }
        key = min(imgs)
        if key not in seen:
            seen.add(key)
            reps.append(key)
            orbit_sum += len(imgs)
    assert orbit_sum == 11440 and len(reps) == 111

    for mod in (101, 103):
        inv_tbl = [0] + [pow(i, -1, mod) for i in range(1, mod)]
        non_antipodal_hits = 0
        for c0 in reps:
            free_orbs = [j for j in range(32) if j not in c0]
            ns = len(free_orbs)
            pts = [4 * c for c in c0]
            rows = [
                (exp_orb[pts[i], free_orbs, :] - exp_orb[pts[0], free_orbs, :]).T
                for i in range(1, 7)
            ]
            rows.append(weights[free_orbs][None, :])
            mat = np.vstack(rows) % mod
            piv_c, free_c = [], []
            r = 0
            for col in range(ns):
                nz = np.flatnonzero(mat[r:, col])
                if len(nz) == 0:
                    free_c.append(col)
                    continue
                p = r + nz[0]
                mat[[r, p]] = mat[[p, r]]
                mat[r] = (mat[r] * inv_tbl[int(mat[r, col])]) % mod
                fac = mat[:, col].copy()
                fac[r] = 0
                mat = (mat - fac[:, None] * mat[r]) % mod
                piv_c.append(col)
                r += 1
            nf = len(free_c)
            if nf == 0:
                continue
            for vals in product((0, 1, -1), repeat=nf):
                if not any(vals) or next(v for v in vals if v != 0) != 1:
                    continue
                w = np.zeros(ns, dtype=np.int64)
                for idx, fc in enumerate(free_c):
                    w[fc] = vals[idx]
                ok = True
                for row_i, pc in enumerate(piv_c):
                    s = (-sum(int(mat[row_i, free_c[k]]) * vals[k] for k in range(nf))) % mod
                    if s == 0:
                        w[pc] = 0
                    elif s == 1:
                        w[pc] = 1
                    elif s == mod - 1:
                        w[pc] = -1
                    else:
                        ok = False
                        break
                if not ok:
                    continue
                full_w = np.zeros(32, dtype=np.int64)
                for idx, oi in enumerate(free_orbs):
                    full_w[oi] = w[idx]
                if not all(full_w[k] == full_w[k + 8] for k in range(8)):
                    non_antipodal_hits += 1
        assert non_antipodal_hits == 0
        print(
            f"mu_64 Case 2B MOD={mod}: reps={len(reps)}, orbit_sum={orbit_sum}, "
            f"non_antipodal_hits={non_antipodal_hits}",
            flush=True,
        )


@cache
def twice_cos(n: int, t: int) -> tuple[int, int]:
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


def exact_ceil_log2_scaled(val: int, scale: int, s: int) -> int:
    p = val ** s
    q = scale ** s
    if p >= q:
        L = max(0, p.bit_length() - q.bit_length())
        while (q << L) < p:
            L += 1
        while L > 0 and (q << (L - 1)) >= p:
            L -= 1
        return L
    m = max(0, q.bit_length() - p.bit_length())
    while (p << m) > q:
        m -= 1
    while (p << (m + 1)) <= q:
        m += 1
    return -m


def exact_floor_log2_scaled(val: int, scale: int, s: int) -> int:
    return -exact_ceil_log2_scaled(scale, val, s)


def verify_anti_deg15_norm() -> None:
    pow2_hi = [0] * LOG_SCALE
    for r in range(LOG_SCALE):
        target = 1 << (r + EXP_SHIFT * LOG_SCALE)
        lo_c, hi_c = 1 << EXP_SHIFT, 1 << (EXP_SHIFT + 1)
        while lo_c < hi_c:
            mid = (lo_c + hi_c) // 2
            if mid ** LOG_SCALE >= target:
                hi_c = mid
            else:
                lo_c = mid + 1
        pow2_hi[r] = lo_c

    # Precompute |t_i - t_j| for i, j in 1..31 and |cot(pi*k*j/64)| = sqrt((2+t_j)/(2-t_j))
    # Note: |cot(pi*k*j/64)|^2 = (2*SCALE_COS + t_{k*j}) / (2*SCALE_COS - t_{k*j})!
    hi_d = np.zeros((16, 32, 32), dtype=np.int64)
    lo_d = np.zeros((16, 32, 32), dtype=np.int64)
    hi_cot = np.zeros((16, 32), dtype=np.int64)
    lo_cot = np.zeros((16, 32), dtype=np.int64)
    for e in range(16):
        k = 2 * e + 1
        for i in range(1, 32):
            ti_lo, ti_hi = twice_cos(64, k * i)
            # |cot| = sqrt((2 + t) / (2 - t)): use exact integer sqrt enclosures!
            num_lo = isqrt(max(0, (2 * SCALE_COS + ti_lo) * SCALE_COS))
            num_hi = isqrt((2 * SCALE_COS + ti_hi) * SCALE_COS) + 1
            den_lo = isqrt(max(0, (2 * SCALE_COS - ti_hi) * SCALE_COS))
            den_hi = isqrt((2 * SCALE_COS - ti_lo) * SCALE_COS) + 1
            assert num_lo > 0 and den_lo > 0
            hi_cot[e, i] = exact_ceil_log2_scaled(num_hi, den_lo, LOG_SCALE)
            lo_cot[e, i] = exact_floor_log2_scaled(num_lo, den_hi, LOG_SCALE)
            for j in range(i + 1, 32):
                tj_lo, tj_hi = twice_cos(64, k * j)
                dl = ti_lo - tj_hi
                dh = ti_hi - tj_lo
                lo_v, hi_v = (dl, dh) if dl > 0 else (-dh, -dl)
                assert lo_v > 0
                hi_d[e, i, j] = hi_d[e, j, i] = exact_ceil_log2_scaled(hi_v, SCALE_COS, LOG_SCALE)
                lo_d[e, i, j] = lo_d[e, j, i] = exact_floor_log2_scaled(lo_v, SCALE_COS, LOG_SCALE)

    masks8 = np.arange(256, dtype=np.int64)[:, None]
    bits8 = ((masks8 >> np.arange(8, dtype=np.int64)) & 1).astype(np.int64)

    worst = 0
    worst_pair = (-1, -1)
    pairs = [(x, y) for x in (1, 2, 4, 8) for y in range(x + 1, 32)]
    for x, y in pairs:
        sites = [j for j in range(1, 32) if j != x and j != y]
        m = len(sites)
        hi_log = hi_d[:, y, sites] - lo_d[:, x, sites]
        lo_log = lo_d[:, y, sites] - hi_d[:, x, sites]
        c_hi_p = hi_cot[:, y] - lo_cot[:, x]
        c_hi_m = hi_cot[:, x] - lo_cot[:, y]

        hi_lo8, hi_hi8 = bits8 @ hi_log[:8], bits8 @ hi_log[8:]
        lo_lo8, lo_hi8 = bits8 @ lo_log[:8], bits8 @ lo_log[8:]
        for c_vec in (c_hi_p, c_hi_m):
            c_lo8, c_hi8 = bits8 @ c_vec[:8], bits8 @ c_vec[8:]
            all_exps = np.empty(65536, dtype=np.int64)
            for h in range(256):
                H = hi_lo8 + hi_hi8[h]
                L = lo_lo8 + lo_hi8[h]
                top7 = np.partition(H, m - 7, axis=1)[:, m - 7:].sum(axis=1)
                bot7 = np.partition(L, 6, axis=1)[:, :7].sum(axis=1)
                all_exps[h * 256:(h + 1) * 256] = top7 - bot7 + (c_lo8 + c_hi8[h])
            max_e = int(all_exps.max())
            base_bits = (max_e // LOG_SCALE) - 40
            total_scaled = 0
            for e_val in all_exps.tolist():
                diff_e = e_val - base_bits * LOG_SCALE
                if diff_e <= 0:
                    total_scaled += 1 << EXP_SHIFT
                else:
                    q, r = divmod(diff_e, LOG_SCALE)
                    total_scaled += pow2_hi[r] << q
            shift = base_bits - EXP_SHIFT
            bnd = (total_scaled << shift) if shift >= 0 else ((total_scaled + (1 << (-shift)) - 1) >> (-shift))
            if bnd > worst:
                worst, worst_pair = bnd, (x, y)
    assert worst < (1 << 151) < PRIME_1 < PRIME_2
    print(
        f"Anti-invariant deg-15 norm (all {len(pairs)} Galois-rep interior pairs, pure integer): "
        f"worst at {worst_pair}, bit_length={worst.bit_length()} < 2^151 < p1 < p2",
        flush=True,
    )


def main() -> None:
    verify_mu64_case2B()
    verify_anti_deg15_norm()
    src = Path(__file__).with_name("probe_quarter_mu64_anti_deg15.cpp")
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "anti_deg15_sieve"
        subprocess.run(["c++", "-O3", "-std=c++17", str(src), "-o", str(exe)], check=True)
        subprocess.run([str(exe)], check=True)


if __name__ == "__main__":
    main()
