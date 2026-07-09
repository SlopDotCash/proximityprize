#!/usr/bin/env python3
"""#466 R317: test whether high-beta heavy depth-3 excess forces a small rational resonance.

For a prime p == 1 mod n, a rational a/b is a subgroup resonance when
`(a / b)^n == 1 mod p`.  At depth three the natural candidates have
`1 <= a,b <= 3`.  This probe parses the complete R305 census and asks whether
every exact-Wick violation above a chosen beta cutoff has such a resonance.
"""

from __future__ import annotations

import argparse
import math
import re
from pathlib import Path


ROW = re.compile(r"p=\s*(\d+).*excess=(\d+)")


def rows(path: Path):
    for line in path.read_text().splitlines():
        match = ROW.search(line)
        if match:
            yield tuple(map(int, match.groups()))


def resonances(p: int, n: int, depth: int) -> list[tuple[int, int]]:
    out = []
    for a in range(1, depth + 1):
        for b in range(1, depth + 1):
            if a == b or math.gcd(a, b) != 1:
                continue
            ratio = a * pow(b, -1, p) % p
            if pow(ratio, n, p) == 1:
                out.append((a, b))
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--beta-min", type=float, default=4.0)
    parser.add_argument(
        "--census", type=Path, default=Path("scripts/probes/_out_466_r305_census_n32.txt")
    )
    args = parser.parse_args()

    headroom = 45 * args.n**2 - 40 * args.n
    considered = heavy = unexplained = 0
    print("# R317 high-beta heavy-resonance inverse test")
    print(
        f"n={args.n} depth={args.depth} beta_min={args.beta_min} "
        f"headroom={headroom} census={args.census}"
    )
    for p, excess in rows(args.census):
        beta = math.log(p) / math.log(args.n)
        if beta <= args.beta_min:
            continue
        considered += 1
        if excess <= headroom:
            continue
        heavy += 1
        rs = resonances(p, args.n, args.depth)
        if not rs:
            unexplained += 1
        print(
            f"heavy p={p} beta={beta:.6f} excess={excess} "
            f"ratio={excess / headroom:.6f} resonances={rs}"
        )
    print(f"summary considered={considered} heavy={heavy} unexplained={unexplained}")
    return 1 if unexplained else 0


if __name__ == "__main__":
    raise SystemExit(main())
