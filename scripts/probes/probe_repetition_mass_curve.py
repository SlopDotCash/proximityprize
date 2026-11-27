#!/usr/bin/env python3
"""Exact-integer certificates for the production repetition-code MCA mass curve."""

from math import comb, isqrt

N = 2**30
FIRST = 2**21


def rich_light_lines(mass, agreements):
    """Largest r below agreements with r*t - choose(r,2) <= mass."""
    discriminant = (2*agreements + 1)**2 - 8*mass
    assert discriminant > 0
    r = (2*agreements + 1 - isqrt(discriminant)) // 2
    if r*agreements - r*(r-1)//2 > mass:
        r -= 1
    assert 0 <= r < agreements
    assert r*agreements - comb(r, 2) <= mass < (r+1)*agreements - comb(r+1, 2)
    return r


def maximum(agreements, length=N):
    """Exact optimum in the proven range from the two integers at the quadratic vertex."""
    vertex = (2*length-1) // (4*agreements-6)
    last = length // (agreements-1)
    rows = []
    for candidate in (vertex, vertex+1):
        centers = min(last, max(1, candidate))
        mass = length - centers*(agreements-1)
        lines = rich_light_lines(mass, agreements)
        assert lines <= agreements-2
        rows.append((centers*mass + comb(centers, 2) + lines, centers, lines))
    return max(rows)


def weak_twice(centers, strong_light_mass, width):
    """Twice the maximum one-heavy contribution for at least one weak center."""
    def value(weak):
        return (2*centers-weak)*(strong_light_mass + weak*width)

    vertex = (2*centers*width - strong_light_mass) // (2*width)
    return max(value(min(centers, max(1, w))) for w in (vertex, vertex+1))


def cut_for_interval(low, high):
    """One cutoff proving the weighted-line upper bound at every integer in a range."""
    lower = maximum(high)[0]
    for divisor in (5, 4, 6, 7, 8, 3, 10, 12, 16, 2):
        gap = low // divisor
        assert 2 < gap <= low
        width = gap-2
        away = N*N // (low*gap)
        max_heavy = N // (low-gap+1)
        if away > lower:  # Zero heavy centers.
            continue
        for h in range(1, max_heavy+1):
            mass = N - h*(low-1)
            multi = comb(h, 2)
            if away + multi + h*(mass + h*width) <= lower:
                continue
            if 2*(away+multi) + weak_twice(h, mass, width) > 2*lower:
                break
            if mass >= 0 and h*(low-away+1) < away-1:
                break
        else:
            return gap
    return None


def certify(first, last):
    pending = [(first, last)]
    intervals = []
    while pending:
        low, high = pending.pop()
        gap = cut_for_interval(low, high)
        if gap is not None:
            intervals.append((low, high, gap))
            continue
        assert low < high, f"no certificate at {low}"
        midpoint = (low+high)//2
        pending.extend(((midpoint+1, high), (low, midpoint)))
    assert intervals[0][0] == first and intervals[-1][1] == last
    assert all(a[1]+1 == b[0] for a, b in zip(intervals, intervals[1:]))
    return intervals


if __name__ == "__main__":
    intervals = certify(FIRST, 2*N//3)
    print(f"{len(intervals)} exact intervals covering t={FIRST}..{2*N//3}")
    for errors, expected in ((805306366, N-2), (805306367, N+2),
                             (939524094, 2*N-7), (939524095, 2*N+10)):
        actual, centers, lines = maximum(N-errors)
        assert actual == expected
        print(f"errors={errors} mass={actual} centers={centers} light_lines={lines}")
    print(f"t={FIRST} mass={maximum(FIRST)[0]}")
    assert maximum(524288) == (549757387265, 1024, 1025)
    print(f"uniform t=524288 mass={maximum(524288)[0]}")
