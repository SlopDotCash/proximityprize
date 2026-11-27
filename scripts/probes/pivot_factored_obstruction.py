#!/usr/bin/env python3
"""Exact-integer verifier for PivotFactoredObstruction.lean:
verifies the sharp Kopparty–Sha Appendix A / core-weighted ordinary mixed-Hasse
obstruction at BOTH second-prime Johnson pivots (half rate 314,491,699 and
quarter rate 536,870,913).
"""

N = 1 << 30
BUDGET = 2 * N

HALF = {
    "name": "Half-rate pivot (1/2)",
    "d": (1 << 29) - 1,
    "e": 314_491_699,
    "t": N - 314_491_699,
    "delta": 1_082_833_961,
    "sharp_radius": 155_925_516,
    "carbon_radius": 110_255_990,
}

QUARTER = {
    "name": "Quarter-rate pivot (1/4)",
    "d": (1 << 28) - 1,
    "e": 536_870_913,
    "t": N - 536_870_913,
    "delta": 1,
    "sharp_radius": 144_115_187_807_420_414,
    "carbon_radius": 72_057_593_769_492_479,
}


def require(cond, msg):
    if not cond:
        raise AssertionError(msg)


def verify_pivot(p):
    d, e, t, delta, r_sharp = p["d"], p["e"], p["t"], p["delta"], p["sharp_radius"]
    require(N - e == t, f"{p['name']}: N - e != t")
    require(t * t == N * d + delta, f"{p['name']}: t^2 != N*d + delta")
    require(2 * t <= N + d, f"{p['name']}: 2*t > N + d")
    # Positive-definiteness guard for the middle-prefix identity:
    require(d * d <= t * (N + 3 * d - 3 * t), f"{p['name']}: mid_row_core PD guard failed")
    # Exact sharp radius endpoint check:
    def quad_cond(r):
        return 4 * r * r * delta + d * d <= 4 * r * d * (N - t)

    require(quad_cond(1), f"{p['name']}: r=1 failed")
    require(quad_cond(r_sharp), f"{p['name']}: r=sharp_radius failed")
    require(not quad_cond(r_sharp + 1), f"{p['name']}: r=sharp_radius+1 should cross")

    # Continuous multi-core Kopparty–Sha obstruction spot-check across K and H <= t:
    for r in (1, 17, 1000, r_sharp):
        for H in (0, d, t - 1, t):
            for K in (0, 1, 2, r // 2, r, (r * t) // d):
                if d * K > r * t:
                    continue
                lhs = N * (r * t - d * K) ** 2 - d * (N * r - K * H) ** 2
                rhs = N * r * r * (t * t - N * d)
                require(lhs <= rhs, f"{p['name']}: continuous obstruction failed at r={r},K={K},H={H}")
                if K > 0:
                    require(lhs < rhs, f"{p['name']}: strict continuous loss failed at r={r},K={K},H={H}")

    # Discrete single-core columnCount <= rowCount spot-check across (r, K, s, v):
    for r in (1, 2, 5, 12, 25):
        for K in range(r + 1):
            W = r * t - d * K
            for s in (r - 1, r, r + 5, 2 * r + 3):
                for v in (0, r - K, r, r + 3, W // d + 2):
                    cols = sum((s + 1 - j) * max(0, W - j * d) for j in range(min(v, s) + 1))
                    row_r = sum((r - j) * (s + 1 - j) for j in range(min(r, s + 1)))
                    row_rk = sum((r - K - j) * (s + 1 - j) for j in range(min(r - K, s + 1)))
                    rows = (N - t) * row_r + t * row_rk
                    require(cols <= rows, f"{p['name']}: discrete failed r={r},K={K},s={s},v={v}")

    print(
        f"[OK] {p['name']}: e={e:,}, t={t:,}, delta={delta:,}, "
        f"sharp_radius={r_sharp:,} (vs Carbon {p['carbon_radius']:,}, "
        f"ratio={r_sharp / p['carbon_radius']:.4f}x)"
    )


def main():
    verify_pivot(HALF)
    verify_pivot(QUARTER)
    require(BUDGET < QUARTER["sharp_radius"], "quarter scalar overflow")
    require(BUDGET < HALF["sharp_radius"] ** 2, "half two-surface overflow")
    print("ALL PivotFactoredObstruction exact-integer checks PASSED.")


if __name__ == "__main__":
    main()
