"""Exact normalized-fibre complement estimates at the second named prime."""

from probe_weighted_hodge_windows import N, monomial_surplus

# (rate denominator, safe errors, first interpolant, second interpolant)
CASES = (
    (2, 299_700_000, (7, 10, 3647), (13, 18, 118)),
    (4, 516_200_000, (6, 12, 28435), (12, 24, 129)),
    (8, 665_900_000, (4, 12, 21302), (8, 24, 87)),
)


TAME_CASES = (
    (2, 301_600_000, (8, 11, 1224), (15, 21, 152)),
    (4, 517_600_000, (7, 13, 7818), (13, 26, 147)),
    (8, 667_400_000, (5, 13, 431), (8, 24, 96)),
)


def check(rate, errors, primary, companion, tame=False):
    t, d = N - errors, N // rate - 1
    r, v, s = primary
    _, v2, a = companion
    ranks = [monomial_surplus(shape, t, d) for shape in (primary, companion)]
    assert min(ranks) > 0
    cutoff = max(errors // 256 + 1, s * v2 + v * a + 1)
    assert t - a*N//cutoff - 3*(a*N//(cutoff-a)) > d
    core = t - 255
    group = 3 if 3*core > N + 2*d else 4
    assert group == 3 or 4*core > N + 4*d
    denominator = 100*(t-d) if tame else 39*t - 40*d
    assert denominator > 0
    worst = (-1, None)
    for heads in range(v + 1):
        head_count = heads*(errors + 1)
        if heads >= group:
            divisor = core + (heads-1)*d
            covered = (heads*core**2 + divisor-1)//divisor
            head_count = min(head_count, heads*N - (heads-1)*covered)
        for total_degree in range(heads, v + 1):
            prices = [0, cutoff]
            for b in range(2, total_degree-heads+1):
                w = r*t - 1 - (total_degree-b)*d
                m = a - heads
                if w < b*d or m < b:
                    prices.append(cutoff)
                    continue
                bx = (2*b-2)*m + 1 - b*(b-1)
                bz = (2*b-2)*w + 1 - b*(b-1)*d
                assert bx > 0 and bz > 0
                numerator = 30*b*(4*m*bx*bz + m*N + bx*bz) + 40*(N-d)*(m+1)
                if tame:
                    penalty = 77 if b >= 3 else 100
                    numerator = penalty*b*(2*m*bx*bz + m*N + bx*bz) + 100*(N-d)*(m+1)
                prices.append(max(cutoff, bx + numerator//denominator))
            best = [0]
            for slot in range(1, total_degree-heads+1):
                best.append(max(prices[b]+best[slot-b] for b in range(1, slot+1)))
            # Scalar-only primary factors may consume up to s further labels.
            count = s + head_count + best[-1]
            if count > worst[0]:
                worst = (count, (heads, total_degree))
    assert worst[0] <= 2*N
    return ranks, cutoff, worst


if __name__ == '__main__':
    for case in CASES:
        print(case[0], case[1], check(*case))
    for case in TAME_CASES:
        print(case[0], case[1], check(*case, tame=True))
