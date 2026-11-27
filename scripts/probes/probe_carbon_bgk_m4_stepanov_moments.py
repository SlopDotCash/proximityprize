#!/usr/bin/env python3
"""Lightweight (<0.2s) verification probe for CarbonBGKM4ConfluentStepanovAndMoments."""

from __future__ import annotations

import re
from pathlib import Path


def check(cond: bool, msg: str = "check failed") -> None:
    if not cond:
        raise AssertionError(msg)


def check_stepanov_and_moments() -> None:
    n = 2**30
    p1 = n * (2**128 + 192) + 1
    p2 = n * (2 * 2**128 + 13) + 1

    # 1. J = 1 degree-2 confluent graded shift-Stepanov parameters:
    a1, b1, c1, d1 = 838860, 2490, 1280, 1621001
    check(0 < a1 <= n and 0 < c1 and a1 * c1 <= n)
    check(a1 - 1 + n * (c1 - 1) < 2**41 < p1 < p2)
    check(d1 <= 2**41)
    check(1 * (d1 * (2 * a1 + (d1 - 1))) < 2 * (b1 * (a1 * c1)))
    deg1 = (a1 - 1) + n * (c1 - 1) + n * (b1 - 1)
    cap1 = deg1 // d1
    check(cap1 == 2495902, f"cap1={cap1}")
    check(cap1 < 2**22)
    check(cap1**3 <= 64 * n**2)

    # 2. J = 4 simultaneous 4-coset shift-Stepanov parameters:
    a4, b4, c4, d4 = 542293, 4060, 1980, 1030530
    check(0 < a4 <= n and 0 < c4 and a4 * c4 <= n)
    check(a4 - 1 + n * (c4 - 1) < 2**41)
    check(4 * (d4 * (2 * a4 + (d4 - 1))) < 2 * (b4 * (a4 * c4)))
    deg4 = (a4 - 1) + n * (c4 - 1) + n * (b4 - 1)
    cap4 = deg4 // d4
    check(cap4 == 6291183, f"cap4={cap4}")

    # 3. Exact integer ceiling for sum-product expansion on mu_{2^30}:
    min_sumset = (n**2 + cap1) // (cap1 + 1)
    check(min_sumset == 461925605526, f"min_sumset={min_sumset}")
    check(min_sumset > 430 * n)

    # 4. Small-prime concrete sanity check: mu_8 subset F_41, check exact diff-autocorr identity
    q = 41
    g_set = [x for x in range(1, q) if pow(x, 8, q) == 1]
    check(len(g_set) == 8)
    for r in (1, 2, 3):
        freq_r = [0] * q
        if r == 1:
            for x in g_set:
                freq_r[x] += 1
        elif r == 2:
            for x in g_set:
                for y in g_set:
                    freq_r[(x + y) % q] += 1
        elif r == 3:
            for x in g_set:
                for y in g_set:
                    for z in g_set:
                        freq_r[(x + y + z) % q] += 1
        freq_next = [sum(freq_r[(d - s) % q] for s in g_set) for d in range(q)]
        e_r = sum(v * v for v in freq_r)
        e_next = sum(v * v for v in freq_next)
        autocorr = [sum(freq_r[e] * freq_r[(e + delta) % q] for e in range(q)) for delta in range(q)]
        diff_cnt = [sum(1 for x in g_set if (x - delta) % q in g_set) for delta in range(q)]
        check(sum(autocorr) == len(g_set) ** (2 * r))
        check(sum(autocorr[1:]) == len(g_set) ** (2 * r) - e_r)
        check(e_next == len(g_set) * e_r + sum(diff_cnt[d] * autocorr[d] for d in range(1, q)))
        sumset_card = sum(1 for v in freq_r if v > 0)
        check(len(g_set) ** (2 * r) <= sumset_card * e_r)

    # 5. Midpoint defect gap at P1 and P2:
    amin = 3 * n**2 - 3 * n
    m_cap = cap1 * n
    for p in (p1, p2):
        lhs = p * (amin + n - 2 * m_cap) - (n * (n - 1)) ** 2
        rhs = 2 * (n - 1) ** 2 * (p - n)
        check(lhs > rhs)

    # 6. Check relative markdown links in companion note:
    md_path = Path("docs/research/proximity-gap/carbon-bgk-m4-confluent-stepanov-and-moments.md")
    text = md_path.read_text(encoding="utf-8")
    for match in re.finditer(r"\]\(([^)]+)\)", text):
        link = match.group(1)
        if not link.startswith(("http://", "https://", "#")):
            target = (md_path.parent / link.split("#")[0]).resolve()
            check(target.exists(), f"Broken relative link: {link} -> {target}")

    print(
        f"[OK] M4 verified: shift J=1 cap={cap1} (<2^22, 20.6% < 3143679), "
        f"J=4 cap={cap4}, |G+G|>={min_sumset} (>430|G|), midpoint & mu_8 identities exact."
    )


if __name__ == "__main__":
    check_stepanov_and_moments()
