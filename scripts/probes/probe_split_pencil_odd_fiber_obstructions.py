#!/usr/bin/env python3
"""Exact arithmetic verification for SplitPencilOddFiberObstructions.lean."""
from __future__ import annotations

from fractions import Fraction
import math

N = 1 << 30
D_EVEN = (1 << 28) - 2
D_ODD = (1 << 28) - 1
P1 = (1 << 158) + 192 * (1 << 30) + 1
P2 = (1 << 159) + 13 * (1 << 30) + 1


def verify_ramification() -> None:
    cases = [
        ("Case1_s2", 6, D_EVEN // 2, 1 << 28, 48017725, 47715727),
        ("Case2a_x2", 3, D_EVEN // 2, 1 << 27, 24282334, 24129615),
        ("OddD_full", 3, D_ODD, 1 << 28, 50263626, 49947503),
        ("OddD_s3", 9, D_ODD // 3, 1 << 28, 46865709, 46570956),
        ("OddD_s5", 15, D_ODD // 5, 1 << 28, 45494047, 45207921),
    ]
    for name, K, m, half_len, t1, t2 in cases:
        assert m % 2 == 1, f"{name}: m must be odd"
        E = (2 * K * m) // (K - 1)
        assert math.floor(half_len * math.log2(E) / 158) + 1 == t1
        assert math.floor(half_len * math.log2(E) / 159) + 1 == t2
        print(f"Ramification {name}: K={K}, m={m:,}, E<={E:,} -> p1 S>={t1:,}, p2 S>={t2:,}")


def verify_odd_divisors_and_excess() -> None:
    divs = sorted(
        {d for i in range(1, math.isqrt(D_ODD) + 1) if D_ODD % i == 0 for d in (i, D_ODD // i)}
    )
    assert len(divs) == 64  # 62 nontrivial proper divisors
    surviving = [d for d in divs if d - 1 >= 44739242]
    assert surviving == [53687091, 89478485, 268435455]
    assert math.gcd(N, D_ODD) == 1

    # Exact orbifold excess floors: 2 * 268435435 / (6 * m - 268435441)
    e5 = Fraction(2 * 268435435, 6 * 53687091 - 268435441)
    e3 = Fraction(2 * 268435435, 6 * 89478485 - 268435441)
    e1 = Fraction(2 * 268435435, 6 * 268435455 - 268435441)
    assert e5 == Fraction(107374174, 10737421) and e5 > 9
    assert e3 == Fraction(536870870, 268435469) and e3 > 1
    assert e1 == Fraction(536870870, 1342177289)
    assert min(e5 / 5, e3 / 3, e1) == e1

    # Signature exclusions
    assert Fraction(2) - Fraction(1, 3947580) < e3
    assert Fraction(2) - Fraction(1, 3947581) > e3
    assert Fraction(1) - Fraction(1, 2) - Fraction(1, 10) - Fraction(1, 29433712) < e1
    assert Fraction(1) - Fraction(1, 2) - Fraction(1, 10) - Fraction(1, 29433713) > e1
    assert 2 * N * D_ODD < (1 << 59) < P1 < P2
    print(f"Odd-D classification verified: 60/62 proper divisors killed; E_5={float(e5):.7f}, E_3={float(e3):.7f}, E_1={float(e1):.9f}")


if __name__ == "__main__":
    verify_ramification()
    verify_odd_divisors_and_excess()
