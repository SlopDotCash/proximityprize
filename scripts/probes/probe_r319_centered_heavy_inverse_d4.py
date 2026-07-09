#!/usr/bin/env python3
"""#466 R319: stress the centered heavy-resonance inverse on depth-4 K-bad primes.

The D4 census calls a prime K-bad when its DC-subtracted energy exceeds
1.05 times the characteristic-zero energy.  That is not the prize's Wick
threshold.  This probe recomputes the actual DC-subtracted Wick ratio and the
centered wraparound/headroom ratio, then checks small rational resonances.
"""

from __future__ import annotations

import argparse
import math
import re
from pathlib import Path


ROW = re.compile(r"^(\d+)\s+\d+\s+[0-9.]+\s+\S+\s+\d+\s+\d+\s+(\d+)\s+")


def has_resonance(p: int, n: int, depth: int) -> bool:
    for a in range(1, depth + 1):
        for b in range(1, depth + 1):
            if a == b or math.gcd(a, b) != 1:
                continue
            if pow(a * pow(b, -1, p) % p, n, p) == 1:
                return True
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--input", type=Path, default=Path("scripts/probes/_out_466_d4_structure.txt"))
    args = parser.parse_args()

    n, r = args.n, args.depth
    if r != 4:
        raise ValueError("the parsed census and closed form are depth four")
    char0 = 105 * n**4 - 630 * n**3 + 1435 * n**2 - 1155 * n
    wick = 105 * n**4
    headroom = wick - char0
    rows = []
    for line in args.input.read_text().splitlines():
        match = ROW.match(line)
        if not match:
            continue
        p, wrap = map(int, match.groups())
        dc = n ** (2 * r) / p
        dc_energy = char0 + wrap - dc
        centered = wrap - dc
        rows.append(
            (dc_energy / wick, centered / headroom, p, wrap, has_resonance(p, n, r))
        )

    if not rows:
        raise ValueError("no census rows parsed")
    max_wick = max(rows)
    max_centered = max(rows, key=lambda row: row[1])
    super_wick = [row for row in rows if row[0] > 1.0]
    resonant = [row for row in rows if row[4]]
    print("# R319 centered heavy-resonance inverse: depth-4 stress")
    print(
        f"n={n} r={r} rows={len(rows)} char0={char0} wick={wick} "
        f"headroom={headroom}"
    )
    print(
        f"max_wick_ratio p={max_wick[2]} ratio={max_wick[0]:.12f} "
        f"centered_headroom_ratio={max_wick[1]:.12f} resonance={max_wick[4]}"
    )
    print(
        f"max_centered_ratio p={max_centered[2]} wick_ratio={max_centered[0]:.12f} "
        f"centered_headroom_ratio={max_centered[1]:.12f} resonance={max_centered[4]}"
    )
    print(
        f"summary super_wick={len(super_wick)} resonant={len(resonant)} "
        f"nonresonant={len(rows) - len(resonant)}"
    )
    return 1 if super_wick and any(not row[4] for row in super_wick) else 0


if __name__ == "__main__":
    raise SystemExit(main())
