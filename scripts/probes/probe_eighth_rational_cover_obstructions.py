#!/usr/bin/env python3
"""Independent verification probe for EighthRationalCoverObstructions.

Verifies:
1. Universal homothetic fiber theorem 2*M + 3*W <= 6*|S| + 4 across all
   partitions of 4 with parts <= 2 and all fiber sizes 1 <= |S| <= 7.
2. Exact regular-image, isolated-singleton-fiber, and partial-involution floors
   under baseline (20,607,410), Sparse-Gauss (397,364), and Blowup+fixed dual (188,424).
3. Exact 3+1 balanced pencil-degree barrier r_pair >= 3k/4 + 4 = 100,663,300
   below 679,477,248 errors.
"""
from itertools import product

N = 2**30
K = 2**27
D = K - 1
BUDGET = 2 * N
W_MIN = 1_610_612_728


def check_universal_fiber():
    for name, ws in [("(1,1,1,1)", [1, 1, 1, 1]), ("(2,1,1)", [2, 1, 1]), ("(2,2)", [2, 2])]:
        p = len(ws)
        for sz in range(1, 8):
            for tup in product(range(p), repeat=sz):
                U = set(tup)
                W = sum(ws[i] for i in tup)
                pairs = {(min(a, b), max(a, b)) for a in U for b in range(p) if a != b}
                M = len(pairs)
                assert 2 * M + 3 * W <= 6 * sz + 4, (name, sz, tup, M, W)
    print("[PASS] homothetic_fiber_universal verified for all partitions and |S| = 1..7")


def check_cover_floors():
    expected = [
        ("baseline", 20_607_410, 660_784_912, 247_828_000, 412_956_912),
        ("sparse-gauss", 397_364, 670_889_935, 268_038_046, 402_851_889),
        ("blowup+fixed", 188_424, 670_994_405, 268_246_986, 402_747_419),
    ]
    for label, other, exp_I, exp_S, exp_P in expected:
        rhs = 2 * (BUDGET + 1 - other) + 3 * W_MIN - 6 * N - 72
        I_min = (rhs + 3) // 4
        S_exact = 2 * I_min - N
        P_max = N - I_min
        assert I_min == exp_I, (label, I_min, exp_I)
        assert P_max == exp_P, (label, P_max, exp_P)
        assert S_exact == exp_S, (label, S_exact, exp_S)
        print(f"[PASS] {label:12s}: |h(H_reg)| >= {I_min:,}, singletons >= {S_exact:,}, P <= {P_max:,}")


def check_three_plus_one_barrier():
    c_min = N - 679_477_247 - 1
    assert c_min == 394_264_576
    r_min = 4 * c_min - N - 3 * D + 1
    assert r_min == 3 * K // 4 + 4 == 100_663_300
    print(f"[PASS] 3+1 balanced pencil barrier below 679,477,248: r_pair >= {r_min:,} (3k/4 + 4)")


if __name__ == "__main__":
    check_universal_fiber()
    check_cover_floors()
    check_three_plus_one_barrier()
    print("ALL RATIONAL COVER CHECKS PASSED")
