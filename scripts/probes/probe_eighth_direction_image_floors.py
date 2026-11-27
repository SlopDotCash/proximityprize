#!/usr/bin/env python3
"""Independent verification probe for EighthDirectionImageFloors.lean."""

import random

n = 1 << 30
k = 1 << 27
d = k - 1
e5k = 671088640
budget = 2 * n
res4 = 189082

def ceil_div(a, b):
    return (a + b - 1) // b

def main():
    # 1. Exact production floors for q = 2..5
    expected = {
        5: (536681827, 626223335, 321933459),
        4: (503127395, 603853715, None),
        3: (447203342, 566571014, None),
        2: (335355235, 492005611, None),
    }
    for q in (5, 4, 3, 2):
        tot_def = 3 * (e5k + 1) + (1 + e5k // q) - (budget + 1 - res4)
        indiv_min = 2 * (3 * k - 1 - d) - tot_def
        max3_min = ceil_div(3 * 2 * (3 * k - 1) - 2 * (2 * d + 2 * (q - 1)) - 2 * tot_def, 3)
        assert indiv_min == expected[q][0], (q, indiv_min, expected[q][0])
        assert max3_min == expected[q][1], (q, max3_min, expected[q][1])
        if q == 5:
            # 5*(3k-5-d) + (3k-1-d) + 5*(budget+1-res4 - 2*(e5k+1)) - (5*(e5k+1) + (e5k+5))
            g03_min = (budget + 1 - res4) - 2 * (e5k + 1)
            lhs = 5 * (3 * k - 5 - d) + (3 * k - 1 - d) + 5 * g03_min - (5 * (e5k + 1) + (e5k + 5))
            z03_min = ceil_div(lhs, 5)
            assert z03_min == expected[5][2], (z03_min, expected[5][2])
            assert 4 * z03_min > n
            assert 2 * max3_min > n
        elif q in (3, 4):
            assert 2 * max3_min > n
        else:
            assert 3 * max3_min > n
        print(f"[PASS] q={q}: min(z01,z02,z12)>={indiv_min:,d} ({indiv_min/n:.4f}n), "
              f"max(z01,z02,z12)>={max3_min:,d} ({max3_min/n:.4f}n)"
              + (f", min(z03,z13,z23)>={expected[5][2]:,d} ({expected[5][2]/n:.4f}n)" if q == 5 else ""))

    # 2. Exact saturated q = 1 opposite-pair involution floors
    gsum_min = budget + 1 - res4
    sum_2z = 3 * (4 * (3 * k - 1) + gsum_min - 4 * (e5k + 1)) - 2 * (4 * d)
    sum_z = ceil_div(sum_2z, 2)
    each_2z = 4 * (3 * k - 1) - 2 * (2 * d) + gsum_min - 4 * (e5k + 1)
    each_z = ceil_div(each_2z, 2)
    max_z = ceil_div(sum_z, 3)
    assert sum_z == 1073458195
    assert each_z == 268340914
    assert max_z == 357819399
    assert 4 * max_z > n
    print(f"[PASS] q=1: sum>={sum_z:,d} ({sum_z/n:.4f}n), each>={each_z:,d} ({each_z/n:.4f}n), "
          f"max>={max_z:,d} ({max_z/n:.4f}n > n/4)")

    # 3. Random finite-set sanity check of multi_slot_subset_image_ge
    rng = random.Random(2026)
    for _ in range(200):
        H = set(range(40))
        C = set(rng.sample(range(40), rng.randint(5, 18)))
        HC = H - C
        A = set(rng.sample(list(HC), rng.randint(0, len(HC))))
        q = rng.randint(1, 5)
        L = {x: rng.randint(0, 6) for x in HC}
        z = dict(L)
        G = {w for w in range(7) if sum(1 for x in HC if L[x] == w) >= q}
        GA = G & {z[x] for x in A}
        assert len(A) + q * len(G) <= len(HC) + q * len(GA)
    print("[PASS] 200 random finite-set multi_slot_subset_image_ge checks")
    print("ALL DIRECTION IMAGE FLOOR CHECKS PASSED")

if __name__ == "__main__":
    main()
