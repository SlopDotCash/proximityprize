#!/usr/bin/env python3
"""Reproduce G206's collision-free weighted-kernel late-alignment cells.

For G=<g> of order n, the nonzero class weights of
    W(t)=#{y in G: 2y-t in G}
are the fiber multiplicities of phi_2(u)=(2-u)^n.  This probe checks phi_2 is
injective at each recorded cell and recomputes the exact A_5,A_6 integers.
"""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import g56_late_alignment_probe as late  # noqa: E402

CELLS = [(8, 113), (16, 2593), (32, 3617)]
EXPECTED = {
    (8, 113): (-13128, -7240),
    (16, 2593): (24201296, -13779712),
    (32, 3617): (-17378716512, -132640776608),
}


def quotient_labels(n: int, p: int) -> list[int]:
    return [pow((2 - u) % p, n, p) if (2 - u) % p else 0
            for u in late.subgroup(p, n)]


def main() -> None:
    for n, p in CELLS:
        labels = quotient_labels(n, p)
        assert len(labels) == n
        assert len(set(labels)) == n
        rows = [late.row(n, p, r) for r in (5, 6)]
        actual = (rows[0]["A"], rows[1]["A"])
        assert actual == EXPECTED[(n, p)]
        assert all(row["maxW"] == 1 for row in rows)
        print(f"n={n} p={p} labels={labels}")
        print(f"  collision_free=True maxW=1 A5={actual[0]} A6={actual[1]}")


if __name__ == "__main__":
    main()
