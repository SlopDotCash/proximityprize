#!/usr/bin/env python3
"""G316 closed formula for the coefficient-2 antipodal-pair model.

G314/G315 identified an antipodal-pair model behind the certified large-field
toy tables. This probe turns that model into a compact coefficient formula.

Let n=2h and pair the roots as {e_j,-e_j}. With u marking the A-subset rank
and v marking the B-subset rank, the local balanced-choice polynomials are

    N = 1 + 2uv + u^2 + v^2 + u^2v^2       (neutral pair)
    U = u + v + u^2v + uv^2                (unit-forced pair)
    D = uv                                  (double-forced pair)

For coefficient 1, every contributing case has even (deg_u-deg_v), so the
adjacent-rank coefficient [u^r v^(r-1)] is zero.

For coefficient 2, define

    T_m(r) = [u^r v^(r-1)] U N^m.

Then the antipodal model dot is

    D_2(h,r) = 2h*T_{h-1}(r) + 4h(h-1)*T_{h-2}(r-1).

The two terms are exactly the same-pair case z=y and the different-pair case
pair(y) != pair(z). This is a formula for the model only, not a proof that a
finite-field cell has no extra modular relations.

For the live ranks, coefficient extraction simplifies further:

    D_2(h,5) = 2h*(11*C(h-1,2) + 161*C(h-1,3) + 406*C(h-1,4))
    D_2(h,6) = 2h*(C(h-1,2) + 81*C(h-1,3) + 786*C(h-1,4) + 1722*C(h-1,5)).
"""
from __future__ import annotations

from collections import defaultdict
from math import comb
from pathlib import Path
from tempfile import gettempdir


NEUTRAL = {(0, 0): 1, (1, 1): 2, (2, 0): 1, (0, 2): 1, (2, 2): 1}
UNIT = {(1, 0): 1, (0, 1): 1, (2, 1): 1, (1, 2): 1}
DOUBLE = {(1, 1): 1}

EXPECTED_N16_ALL_RANKS = [
    16,
    576,
    8064,
    64064,
    321216,
    1064448,
    2369472,
    3544608,
    3544608,
    2369472,
    1064448,
    321216,
    64064,
    8064,
    576,
]

EXPECTED_R56 = {
    16: {5: 321_216, 6: 1_064_448},
    32: {5: 20_115_200, 6: 200_992_512},
    64: {5: 864_230_400, 6: 20_331_698_688},
    128: {5: 31_776_632_832, 6: 1_609_610_978_304},
}


def neutral_coeff(m: int, a_degree: int, b_degree: int) -> int:
    """Return [u^a_degree v^b_degree] N^m for N=1+2uv+u^2+v^2+u^2v^2."""
    if m < 0 or a_degree < 0 or b_degree < 0:
        return 0
    total = 0
    # x counts 2uv choices, y counts u^2, z counts v^2, w counts u^2v^2.
    for w in range(min(a_degree, b_degree) // 2 + 1):
        max_x = min(a_degree - 2 * w, b_degree - 2 * w)
        for x in range(max_x + 1):
            if (a_degree - x - 2 * w) % 2:
                continue
            if (b_degree - x - 2 * w) % 2:
                continue
            y = (a_degree - x - 2 * w) // 2
            z = (b_degree - x - 2 * w) // 2
            used = x + y + z + w
            if used > m:
                continue
            total += (
                comb(m, x)
                * comb(m - x, y)
                * comb(m - x - y, z)
                * comb(m - x - y - z, w)
                * (2 ** x)
            )
    return total


def unit_tail(m: int, r: int) -> int:
    """Return T_m(r) = [u^r v^(r-1)] U N^m."""
    if m < 0:
        return 0
    return (
        neutral_coeff(m, r - 1, r - 1)
        + neutral_coeff(m, r, r - 2)
        + neutral_coeff(m, r - 2, r - 2)
        + neutral_coeff(m, r - 1, r - 3)
    )


def coeff1_antipodal_dot(_h: int, _r: int) -> int:
    return 0


def coeff2_antipodal_dot(h: int, r: int) -> int:
    same_pair = 2 * h * unit_tail(h - 1, r)
    different_pair = 4 * h * (h - 1) * unit_tail(h - 2, r - 1)
    return same_pair + different_pair


def coeff2_r56_closed(n: int, r: int) -> int:
    assert n % 2 == 0
    h = n // 2
    if r == 5:
        return n * (
            11 * comb(h - 1, 2)
            + 161 * comb(h - 1, 3)
            + 406 * comb(h - 1, 4)
        )
    if r == 6:
        return n * (
            comb(h - 1, 2)
            + 81 * comb(h - 1, 3)
            + 786 * comb(h - 1, 4)
            + 1722 * comb(h - 1, 5)
        )
    raise ValueError("closed form currently recorded only for ranks 5 and 6")


def signed_coordinate(index: int, pair: int, n: int) -> int:
    half = n // 2
    if index == pair:
        return 1
    if index == pair + half:
        return -1
    return 0


def local_balanced_choices(n: int, pair: int, y: int, z: int, coefficient: int) -> list[tuple[int, int]]:
    base = coefficient * signed_coordinate(y, pair, n) - signed_coordinate(z, pair, n)
    out: list[tuple[int, int]] = []
    for a_mask in range(4):
        for b_mask in range(4):
            delta = base
            a_count = 0
            b_count = 0
            if a_mask & 1:
                delta -= 1
                a_count += 1
            if a_mask & 2:
                delta += 1
                a_count += 1
            if b_mask & 1:
                delta += 1
                b_count += 1
            if b_mask & 2:
                delta -= 1
                b_count += 1
            if delta == 0:
                out.append((a_count, b_count))
    return out


def brute_antipodal_dot(n: int, r: int, coefficient: int) -> int:
    half = n // 2
    total = 0
    for y in range(n):
        for z in range(n):
            dp: dict[tuple[int, int], int] = {(0, 0): 1}
            for pair in range(half):
                choices = local_balanced_choices(n, pair, y, z, coefficient)
                next_dp: defaultdict[tuple[int, int], int] = defaultdict(int)
                for (a_rank, b_rank), value in dp.items():
                    for a_count, b_count in choices:
                        aa = a_rank + a_count
                        bb = b_rank + b_count
                        if aa <= r and bb <= r - 1:
                            next_dp[(aa, bb)] += value
                dp = dict(next_dp)
            total += dp.get((r, r - 1), 0)
    return total


def emit(handle, line: str = "") -> None:
    print(line, flush=True)
    handle.write(line + "\n")
    handle.flush()


def verify_parity(handle) -> None:
    assert all((a - b) % 2 == 0 for a, b in NEUTRAL)
    assert all((a - b) % 2 == 0 for a, b in DOUBLE)
    assert all((a - b) % 2 == 1 for a, b in UNIT)
    emit(handle, "parity check: N,D are even and U is odd in deg_u-deg_v")
    emit(handle, "coefficient 1 cases N^h, D*N^(h-1), U^2*N^(h-2) cannot hit adjacent rank")


def verify_against_brute_model(handle) -> None:
    emit(handle, "formula vs brute antipodal model")
    for r, expected in enumerate(EXPECTED_N16_ALL_RANKS, start=1):
        formula = coeff2_antipodal_dot(8, r)
        brute = brute_antipodal_dot(16, r, 2)
        zero = brute_antipodal_dot(16, r, 1)
        assert formula == brute == expected
        assert coeff1_antipodal_dot(8, r) == zero == 0
    emit(handle, f"n=16 coefficient=2 all ranks: {EXPECTED_N16_ALL_RANKS}")

    for n in (32,):
        h = n // 2
        for r in (5, 6):
            formula = coeff2_antipodal_dot(h, r)
            brute = brute_antipodal_dot(n, r, 2)
            zero = brute_antipodal_dot(n, r, 1)
            assert formula == brute == EXPECTED_R56[n][r]
            assert coeff1_antipodal_dot(h, r) == zero == 0
            emit(handle, f"n={n} r={r} formula=brute={formula}")


def emit_r56_formula_table(handle) -> None:
    emit(handle, "closed-form coefficient-2 predictions for ranks 5 and 6")
    for n, rows in EXPECTED_R56.items():
        h = n // 2
        r5 = coeff2_antipodal_dot(h, 5)
        r6 = coeff2_antipodal_dot(h, 6)
        assert coeff2_r56_closed(n, 5) == r5
        assert coeff2_r56_closed(n, 6) == r6
        assert r5 == rows[5]
        assert r6 == rows[6]
        emit(handle, f"n={n} h={h} r=5 dot={r5} r=6 dot={r6}")


def main() -> None:
    out_dir = Path(gettempdir()) / "arklib-reports"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "g316_antipodal_closed_formula.out"

    with out_path.open("w", encoding="utf-8") as handle:
        emit(handle, "G316 antipodal closed formula")
        verify_parity(handle)
        verify_against_brute_model(handle)
        emit_r56_formula_table(handle)
        emit(
            handle,
            "PASS: coefficient 1 vanishes by parity in the antipodal model, and "
            "coefficient 2 is given by D_2(h,r)=2h*T_{h-1}(r)+4h(h-1)*T_{h-2}(r-1).",
        )

    print(f"wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
