#!/usr/bin/env python3
"""Independent verification probe for EighthBlowupDualWindow.lean."""

n = 1 << 30
k = 1 << 27
d = k - 1
budget = 2 * n

def ceil_div(a, b):
    return (a + b - 1) // b

def row_count(s, r):
    return sum((r - j) * (s + 1 - j) for j in range(r))

def col_count(s, b, W):
    return sum((s + 1 - j) * (W - j * d) for j in range(b + 1))

def blowupH(b, W, t0):
    ex = max(0, W - t0)
    return (6 * b + 2) * W - 3 * b * b * d - (3 * ex * ex) // t0 - 2 * ex

WINDOWS = [
    dict(name="W0 671M-1 Safe", e=671088639, r1=6, b1=16, s1=335, r2=10, b2=29, s2=126,
         L=335, lin=17, res4=189082, bound=2125303109, pred=True, h1116=True, h41=True,
         alphas=[1188, 1003, 918, 717, 698, 479, 406, 463, 408, 418, 185, 133, 226, 129, 127, 17, 17],
         betas =[9072, 9150, 8494, 8979, 7320, 7799, 6924, 5117, 4661, 3159, 6032, 6003, 2109, 3164, 411, 0, 0]),
    dict(name="W1 671M 5k",     e=671088640, r1=6, b1=16, s1=335, r2=10, b2=29, s2=126,
         L=335, lin=17, res4=189082, bound=2125303112, pred=False, h1116=True, h41=True,
         alphas=[1188, 1003, 918, 717, 698, 479, 406, 463, 408, 418, 185, 133, 226, 129, 127, 17, 17],
         betas =[9072, 9150, 8494, 8979, 7320, 7799, 6924, 5117, 4661, 3159, 6032, 6003, 2109, 3164, 411, 0, 0]),
    dict(name="W2 677.92M 1116", e=677920000, r1=8, b1=23, s1=680, r2=14, b2=41, s2=244,
         L=680, lin=18, res4=711893, bound=2147458563, pred=False, h1116=True, h41=False,
         alphas=[2952, 2607, 2704, 3003, 2265, 1671, 1315, 1837, 999, 1265, 766, 730, 700, 463, 426, 478, 374, 258, 322, 247, 245, 243, 18, 18],
         betas =[10980, 11664, 7502, 723, 6379, 9746, 10626, 711, 11092, 4465, 10800, 9320, 7656, 10626, 9379, 5496, 5928, 7264, 1356, 900, 415, 252, 0, 0]),
    dict(name="W3 679.477M-1",  e=679477247, r1=9, b1=25, s1=887, r2=16, b2=46, s2=296,
         L=1300, lin=18, res4=1090505, bound=2136590428, pred=False, h1116=False, h41=False,
         alphas=[3368, 3654, 3960, 2381, 3347, 2958, 1653, 2356, 1809, 1779, 1575, 1186, 1033, 770, 615, 466, 543, 664, 306, 374, 320, 300, 298, 296, 18, 18],
         betas =[17393, 10030, 2058, 18752, 1752, 1455, 15370, 1397, 7217, 4610, 5148, 9690, 9940, 13018, 14100, 15455, 10360, 2790, 12510, 6094, 4416, 650, 537, 394, 0, 0]),
]

LADDER = [(2, 1, 6, 1, 8), (3, 2, 10, 4, 20), (4, 2, 15, 4, 40),
          (5, 3, 21, 10, 70), (6, 4, 28, 20, 112), (8, 5, 45, 35, 240), (10, 6, 66, 56, 440)]

def collinear_mass(w, j):
    if j == 0:
        return 0
    if j <= 2:
        return j * (w["e"] + 1)
    c = (n - w["e"]) - w["e"] // w["L"]
    u = ceil_div(j * c * c, c + (j - 1) * d)
    return min(j * (w["e"] + 1), j * n - (j - 1) * u)

def ord_head_mass(w, j):
    if j <= 3:
        return j * (w["e"] + 1)
    if j == 4:
        base = collinear_mass(w, 4)
        if w["pred"]:
            return max(base, 2125114027)
        if w["h1116"]:
            return max(base, 3 * (w["e"] + 1) + (1 + w["e"] // 6))
        return max(base, 3 * (w["e"] + 1) + (1 + w["e"] // 7))
    if j == 5:
        base = collinear_mass(w, 5)
        return max(base, 2058021547) if w["h41"] else base
    return collinear_mass(w, j)

def factor_unit_price(w, j, b, m):
    t = n - w["e"]
    miss = w["e"] // w["L"]
    W = min(w["r1"] * t - 1 - j * d, b * t - 1)
    H = blowupH(b, W, t)
    R = (2 * b - 1) * n
    if m <= 2:
        return 4 * b - 2 + 2 + ceil_div(5 * (R + 2 * H), 5 * t - n - 6 * d)
    best = 10**18
    for (s, a, h, Ca, Es) in LADDER:
        if m > s * (s - 1):
            p = min(j, s + 1)
            gap = a * h * t - (Ca * n + Es * d + a * p * miss)
            assert gap > 0
            pr = 4 * b - 2 + 2 * s * b + ceil_div((h - p) * (a * R + s * H), gap)
            best = min(best, pr)
    return best

def main():
    checks = 0
    for w in WINDOWS:
        t = n - w["e"]
        miss = w["e"] // w["L"]
        core = t - miss
        sur1 = col_count(w["s1"], w["b1"], w["r1"] * t) - n * row_count(w["s1"], w["r1"])
        sur2 = col_count(w["s2"], w["b2"], w["r2"] * t) - n * row_count(w["s2"], w["r2"])
        assert sur1 > 0 and sur2 > 0
        assert max(w["s1"], w["s2"]) <= w["L"]
        assert 4 * n <= (w["lin"] - 1) * (t - d)
        assert 15 * core > 3 * n + 20 * d
        assert 13 * core > 3 * n + 13 * d
        assert 5 * t > n + 6 * d
        assert w["bound"] < budget

        max_tot = 0
        for j in range(w["b1"] + 1):
            a = w["alphas"][j]
            be = w["betas"][j]
            fixed = w["s1"] + (w["s1"] * w["b2"] + w["b1"] * w["s2"]) + (w["b1"] - j) * w["L"]
            res = fixed + (w["s2"] - j) * a + (w["b1"] - j) * be
            if j == 4:
                assert res == w["res4"], f"{w['name']}: res4={res} != {w['res4']}"
            tot = ord_head_mass(w, j) + res
            assert tot <= w["bound"], f"{w['name']} j={j}: tot={tot} > {w['bound']}"
            max_tot = max(max_tot, tot)
            assert w["lin"] <= a
            if w["b1"] - j >= 2:
                assert (w["s2"] - j) + (w["b2"] - j) <= a
            for b in range(2, w["b1"] - j + 1):
                assert b * d <= w["r1"] * t - 1 - j * d
                for m in range(b, w["s2"] - j + 1):
                    u = factor_unit_price(w, j, b, m)
                    assert m * u <= m * a + b * be, f"{w['name']} j={j} b={b} m={m}"
                    checks += 1
        assert max_tot == w["bound"]
        print(f"[PASS] {w['name']:16s} e={w['e']:,d} sur1={sur1:,d} sur2={sur2:,d} "
              f"res4={w['res4']:,d} max={max_tot:,d} (slack={budget - max_tot:+,d})")

    # Verify sharpened 671,088,640 floors from res4 = 189,082
    res4 = 189082
    B_min = ceil_div(budget + 1 - res4 - 3 * (n - 4 * d), 2)
    assert B_min == 268340910 and 2 * d - B_min == 94544
    coll_max = 3 * (671088640 + 1) + (1 + 671088640 // 5) - (budget + 1 - res4)
    assert coll_max == 189085
    img_min = ceil_div(2 * (budget + 1 - res4) + 3 * (12 * k - 8) - 6 * n - 72, 4)
    assert img_min == 670994076
    assert 2 * img_min - n == 268246328
    assert n - img_min == 402747748
    print(f"[PASS] Sharpened floors: B>={B_min:,d} (2d-B<={2*d-B_min:,d}), "
          f"(1,1,1,5) coll<={coll_max:,d}, |h(H_reg)|>={img_min:,d}, "
          f"singletons>={2*img_min-n:,d}, P<={n-img_min:,d}")
    print(f"ALL BLOWUP-DUAL CHECKS PASSED ({checks:,d} exact (j, b, m) factor inequalities verified)")

if __name__ == "__main__":
    main()
