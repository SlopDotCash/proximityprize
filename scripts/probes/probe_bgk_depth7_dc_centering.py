#!/usr/bin/env python3
"""Exact arithmetic audit of the production depth-7 coset amplification.

The amplification input is

    n * |eta_b|^14 <= A7,       A7 = q * E7 - n^14.

For ``|eta_b|^2 <= 2^51`` it is therefore sufficient, and sharp at the
level of this inequality, that ``A7 <= n * (2^51)^7 = 2^387``.

This probe compares that exact centered threshold with:

* the invalid old *raw* bound ``E7 <= 2^18 n^7``; and
* the repaired centered residual ``A7 <= 2^18 q n^7``.

All calculations are integer-only and deterministic.
"""

from __future__ import annotations


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def main() -> None:
    n = 2**30
    q = n * (2**128 + 192) + 1
    depth = 7
    target_sq = 2**51
    flat_constant = 2**18
    wick_constant = 135135  # 13!!

    n7 = n**depth
    dc = n ** (2 * depth)
    sharp_off_budget = n * target_sq**depth

    # Any actual energy satisfies q*E7 >= n^14 because the difference is the
    # nonprincipal moment, a sum of nonnegative terms.
    dc_floor = ceil_div(dc, q)

    old_raw_cap = flat_constant * n7
    old_forces_negative_off_moment = q * old_raw_cap < dc

    # Exact raw-energy form of the sharp centered sufficient condition.
    sharp_raw_max = (dc + sharp_off_budget) // q

    # Repaired residual A7 <= 2^18*q*n^7 and its division-free/raw form.
    flat_off_budget = flat_constant * q * n7
    flat_raw_max = (dc + flat_off_budget) // q
    flat_raw_max_closed = dc // q + flat_constant * n7

    # Largest integral C for a residual A7 <= C*q*n^7 at the exact q.
    exact_max_constant = sharp_off_budget // (q * n7)

    assert n == 1073741824
    assert 2**158 < q < 2**159
    assert n7 == 2**210
    assert dc == 2**420
    assert sharp_off_budget == 2**387
    assert old_raw_cap == 2**228
    assert old_forces_negative_off_moment
    assert old_raw_cap < dc_floor
    assert 2**261 < dc_floor < 2**262
    assert 2**33 * old_raw_cap < dc_floor < 2**34 * old_raw_cap
    assert flat_off_budget <= sharp_off_budget
    assert flat_raw_max == flat_raw_max_closed
    assert flat_raw_max <= sharp_raw_max
    assert flat_raw_max - dc_floor == old_raw_cap - 1
    assert exact_max_constant == 2**19 - 1
    assert (exact_max_constant + 1) * q * n7 > sharp_off_budget
    assert wick_constant < flat_constant < 2 * wick_constant
    assert q * wick_constant * n7 < flat_off_budget

    print("BGK_DEPTH7_DC_CENTERING_AUDIT")
    print(f"n={n}")
    print(f"q={q}")
    print(f"qRange=2^158<q<2^159:{2**158 < q < 2**159}")
    print(f"n^7={n7}=2^210")
    print(f"n^14={dc}=2^420")
    print(f"targetSquared={target_sq}=2^51")
    print(f"sharpOffMomentBudget=n*(targetSquared)^7={sharp_off_budget}=2^387")
    print("sharpCenteredCondition=q*E7-n^14<=2^387")
    print(f"dcEnergyFloor=ceil(n^14/q)={dc_floor}")
    print(f"oldRawCap=2^18*n^7={old_raw_cap}=2^228")
    print(f"oldRawCapBelowDCFloor={old_raw_cap < dc_floor}")
    print(f"oldRawCapForces_qE7_lt_n14={old_forces_negative_off_moment}")
    print("oldRawGap=dcFloor/oldRawCap is strictly between 2^33 and 2^34")
    print(f"sharpRawEnergyMax=floor((n^14+2^387)/q)={sharp_raw_max}")
    print(f"flatConstant={flat_constant}=2^18")
    print(f"flatOffMomentBudget=2^18*q*n^7={flat_off_budget}")
    print(f"flatOffBudgetAtMostSharp={flat_off_budget <= sharp_off_budget}")
    print(f"flatRawEnergyMax=floor((n^14+2^18*q*n^7)/q)={flat_raw_max}")
    print(f"flatRawEnergyMaxClosed=floor(n^14/q)+2^18*n^7={flat_raw_max_closed}")
    print(f"flatHeadroomAboveDCFloor={flat_raw_max - dc_floor}=2^18*n^7-1")
    print(f"exactProductionMaxIntegralConstant={exact_max_constant}=2^19-1")
    print("uniformPowerOfTwoConstantFrom_q_le_2^159=2^18")
    print(f"wickConstant13DoubleFactorial={wick_constant}")
    print(f"flatToWickRatio={flat_constant}/{wick_constant}")
    print(f"wickBelowFlat={wick_constant < flat_constant}")
    print("VERDICT=old raw residual impossible; corrected DC-subtracted residual arithmetically sufficient")


if __name__ == "__main__":
    main()
