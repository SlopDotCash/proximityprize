#!/usr/bin/env python3
"""Certify affine dimensions of potential lists just beyond the named safe counts."""

N = 2**30
# Rate denominator, budget in units of N, errors, required rank, last certified cap.
CASES = (
    (2, 1, 314491700, 58, 886009082),
    (2, 2, 314491700, 60, 1772018175),
    (4, 1, 536870914, 29, 536870916),
    (4, 2, 536870914, 30, 1073741840),
    (8, 1, 694116763, 20, 440738901),
    (8, 2, 694116764, 21, 1246598273),
    (16, 1, 805306371, 15, 357913949),
    (16, 2, 805306371, 16, 1431655816),
)


def certificate(n, t, d, previous, size):
    """The least forced number of constant sites and the shortened moment test."""
    assert previous < size
    gap = size - previous
    common = max(0, (size*t - previous*n + gap - 1) // gap)
    if common > d:
        return common, True
    return common, size * (t-common)**2 > (n-common) * (t-common + (size-1)*(d-common))


def profile(n, t, d, budget):
    previous = 1
    rows = []
    while previous <= budget:
        low = previous + 1
        high = previous * (n-d) // (t-d) + 1
        while low < high:
            middle = (low + high) // 2
            if certificate(n, t, d, previous, middle)[1]:
                high = middle
            else:
                low = middle + 1
        common, excluded = certificate(n, t, d, previous, low)
        # The proof needs only this specific exclusion. Every larger list
        # has a sublist of exactly this size at no greater affine dimension.
        assert excluded
        assert common == 0 or low*t > (common-1)*low + (n-common+1)*previous
        rows.append((low - 1, common))
        previous = low - 1
    return rows


if __name__ == "__main__":
    for rate, multiple, errors, rank, cap in CASES:
        rows = profile(N, N-errors, N//rate-1, multiple*N)
        assert len(rows) == rank and rows[-2][0] == cap
        print(f"1/{rate} B={multiple}n e={errors} rank>={rank} "
              f"cap_at_rank_{rank-1}={cap}")
