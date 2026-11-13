#!/usr/bin/env python3
"""Check the F101 band-3 boundary quadric from #357 DISPROOF_LOG.

The log states that, after normalizing four bad scalars to
gamma = (0, 1, g, h), the determinant condition is

  Q(g,h) = g^2 h^2 + 294 g^2 h + 105 g^2
           - 296 g h^2 - 504 g h + 400 h^2

and that over F_101 there are 196 admissible points, with (g,h)=(2,33)
one end-to-end witness.
"""

P = 101


def q(g: int, h: int, p: int = P) -> int:
    return (
        g * g * h * h
        + 294 * g * g * h
        + 105 * g * g
        - 296 * g * h * h
        - 504 * g * h
        + 400 * h * h
    ) % p


def main() -> None:
    zeros = [(g, h) for g in range(P) for h in range(P) if q(g, h) == 0]
    distinct_scalars = [
        (g, h) for (g, h) in zeros if len({0, 1, g, h}) == 4
    ]
    nondegenerate = [
        (g, h)
        for (g, h) in distinct_scalars
        if g not in (0, 1) and h not in (0, 1) and g != h
    ]

    print(f"raw zeros: {len(zeros)}")
    print(f"distinct normalized scalars: {len(distinct_scalars)}")
    print(f"nondegenerate scalar points: {len(nondegenerate)}")
    print(f"Q(2,33) mod 101 = {q(2, 33)}")
    print("(2,33) in distinct normalized scalars:", (2, 33) in distinct_scalars)
    print("first 20 distinct points:", distinct_scalars[:20])


if __name__ == "__main__":
    main()
