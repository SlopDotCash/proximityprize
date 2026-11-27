#!/usr/bin/env python3
"""Exact arithmetic verifier for CarbonListTightFirstOrder.lean (<0.5s, -O safe)."""


def check(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def capped_tent(L: int, w: int) -> int:
    if 2 * w <= L + 1:
        return w * (L + 1 - w)
    return (L + 1) ** 2 // 4


def row_slots(n: int, m: int, M: int, mu: int, h: int) -> int:
    return sum(
        n * capped_tent(max(0, m - max(0, t - M)), min(t, M) + 1) * max(0, h + 1 - t)
        for t in range(mu + 1)
    )


def col_slots(k: int, A: int, m: int, M: int, mu: int, h: int) -> int:
    return sum(
        (min(t, M) + 1) * max(0, m * A - k * t) * max(0, h + 1 - t)
        for t in range(mu + 1)
    )


def tight_stage_one_unit(k: int, j: int, r: int) -> int:
    if j <= 1:
        return 1
    b0 = 2 * k * (j - 1)
    c0 = min(b0, k * (2 * r - 1))
    return (j - r) * c0 + r * b0


def tight_order_zero_units(mu: int, M: int) -> int:
    m0 = min(M, mu)
    return sum(range(1, mu - m0 + 1))


def tight_order_one_units(k: int, mu: int, M: int) -> int:
    m0 = min(M, mu)
    return sum(tight_stage_one_unit(k, (mu - m0) + r, r) for r in range(1, m0 + 1))


def min_tight_c(N: int, k: int, A: int, mu: int, M: int) -> int:
    z0 = tight_order_zero_units(mu, M)
    z1 = tight_order_one_units(k, mu, M)
    num = z0 * (A - k) + z1 * (N - k)
    den = N * (A - k)
    return (num + den - 1) // den


def main() -> None:
    existing = [
        ("128-half", 128, 64, 89, 43, 12, 59, 1426, 173373, 19522),
        ("128-quarter", 128, 32, 61, 35, 15, 66, 1217, 113975, 21491),
        ("128-eighth", 128, 16, 42, 26, 13, 67, 1181, 58872, 11002),
        ("128-sixteenth", 128, 8, 29, 22, 13, 79, 1321, 52349, 8811),
        ("4096-half", 4096, 2048, 2834, 116, 35, 160, 10333, 3722270, 441892),
        ("4096-quarter", 4096, 1024, 1930, 112, 50, 210, 13205, 3891790, 755543),
        ("4096-eighth", 4096, 512, 1316, 108, 59, 277, 16613, 4624878, 929137),
        ("4096-sixteenth", 4096, 256, 901, 104, 67, 365, 22123, 5864546, 1077546),
        ("4096w-half", 4096, 2048, 2827, 824, 254, 1137, 471498, 1369562863, 164423839),
        ("4096w-quarter", 4096, 1024, 1922, 612, 278, 1148, 360879, 649560740, 127463408),
        ("4096w-eighth", 4096, 512, 1308, 876, 483, 2237, 1058306, 2486297660, 503349611),
        ("4096w-sixteenth", 4096, 256, 895, 488, 321, 1705, 470485, 615760719, 115572934),
    ]
    for name, N, k, A, m, M, mu, h, old_c, exp_c in existing:
        rs = row_slots(N, m, M, mu, h)
        cs = col_slots(k, A, m, M, mu, h)
        check(rs < cs, f"Slot check failed for {name}: {rs} >= {cs}")
        c = min_tight_c(N, k, A, mu, M)
        check(c == exp_c, f"C mismatch for {name}: got {c}, expected {exp_c}")
        check(c < old_c, f"Not smaller for {name}")

    fine65536 = [
        ("65536-half", 65536, 32768, 45222, 1650, 495, 2274, 121442956, 1254436992),
        ("65536-quarter", 65536, 16384, 30735, 1200, 540, 2249, 2046046579, 944087037),
        ("65536-eighth", 65536, 8192, 20925, 850, 467, 2164, 144172924, 455358934),
        ("65536-sixteenth", 65536, 4096, 14310, 650, 422, 2268, 467160053, 266313397),
    ]
    for name, N, k, A, m, M, mu, h, exp_c in fine65536:
        rs = row_slots(N, m, M, mu, h)
        cs = col_slots(k, A, m, M, mu, h)
        check(rs < cs, f"Slot check failed for {name}: {rs} >= {cs}")
        c = min_tight_c(N, k, A, mu, M)
        check(c == exp_c, f"C mismatch for {name}: got {c}, expected {exp_c}")
        check(c < (1 << 31), f"Expected C < 2^31 for {name}")

    low4096 = [
        ("4096-low-half", 4096, 2048, 2881, 13, 3, 18, 7021, 407),
        ("4096-low-quarter", 4096, 1024, 2007, 12, 3, 23, 4874, 341),
        ("4096-low-eighth", 4096, 512, 1401, 10, 3, 27, 15246, 263),
        ("4096-low-sixteenth", 4096, 256, 980, 9, 3, 34, 25721, 222),
    ]
    for name, N, k, A, m, M, mu, h, exp_c in low4096:
        rs = row_slots(N, m, M, mu, h)
        cs = col_slots(k, A, m, M, mu, h)
        check(rs < cs, f"Slot check failed for {name}: {rs} >= {cs}")
        c = min_tight_c(N, k, A, mu, M)
        check(c == exp_c, f"C mismatch for {name}: got {c}, expected {exp_c}")

    print("ALL CarbonListTightFirstOrder checks passed!")


if __name__ == "__main__":
    main()
