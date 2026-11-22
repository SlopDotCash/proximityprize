#!/usr/bin/env python3
"""Exact certificates for the tangent-head budget ladder at length 2**30.

For a finite field with at least 2**(128 + beta) elements the 128-bit integer
budget is at least 2**beta.  The rows need characteristic at least 2**47,
which every prime field of that size has.  Each row below gives an error count e, two mixed
Hasse interpolant shapes (r, v, s), and certifies that every received pair on
every injective domain of length 2**30 has at most 2**beta bad labels at e
errors.  The allocation argument is that of
docs/research/proximity-gap/weighted-hodge-windows.md with the cap of
Theorem D' (docs/research/proximity-gap/section-incidence-hodge-index.md)
for a nonlinear factor, and one further input: rich affine heads have joint
cores of size at least C = t - 255 that pairwise meet in at most d sites, so
there are at most n (C - d) / (C^2 - n d) of them.

The certificate is the proportional-price test used in the Lean window
files: for j rich heads and total value degree l, every value degree b costs
at most its share b / (l - j) of the budget left by the heads.

All arithmetic is exact.  Checks are explicit calls, so the script also runs
under `python3 -O`.  Pass --deep to include the entries at beta = 52 and 56.
"""

N = 2**30
CHECKS = 0

JOHNSON_LADDER = {
    # beta: safe error counts of the weighted Johnson ladder at rates 1/2, 1/4, 1/8, 1/16
    36: (264305680, 441001106, 590558004, 709234733),
    40: (286064053, 497724075, 654203879, 768608494),
    44: (302702397, 521162467, 678319226, 791028984),
    48: (309697726, 530597867, 687862086, 799681249),
    56: (313729682, 535880485, 693133819, 804424509),
    64: (314371491, 536714875, 693962012, 805167589),
    80: (314488717, 536867042, 694112924, 805302928),
}
JOHNSON_COUNT = {2: 314491699, 4: 536870913, 8: 694116762, 16: 805306370}


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise SystemExit(f'CHECK FAILED: {message}')


def surplus(shape, t, d):
    r, v, s = shape
    cols = sum((s-j+1)*max(0, r*t-j*d) for j in range(v+1))
    rows = N*sum((r-j)*(s+1-j) for j in range(r))
    return cols-rows


def tangent_cap(b, m, w, t, d):
    bx = (2*b-2)*m-b*(b-1)+1
    bz = (2*b-2)*w-b*(b-1)*d+1
    budget = 2*bx*bz+b*(w*(m-b)+m*(w-b*d))
    return bx+(m*N*(2*t+N)+2*budget*(t+N))//(t*t-N*d)


def certify(rate, beta, errors, outer, secondary):
    """Return the largest allocation total found by the price test."""
    budget = 2**beta
    d = N//rate-1
    t = N-errors
    r, v, s = outer
    _, va, a = secondary
    check(t*t > N*d, 'below the Johnson radius')
    check(surplus(outer, t, d) > 0 and surplus(secondary, t, d) > 0,
          'nonzero interpolants')
    cutoff = max(errors//256+1, s*va+v*a+1)
    check(t-a*N//cutoff-3*(a*N//(cutoff-a)) > d, 'affine-head test')
    core = t-255
    check(core*core > N*d, 'rich cores are above the Johnson size')
    if 3*core > N+2*d:
        group = 3
    elif 4*core > N+4*d:
        group = 4
    else:
        group = None
    rich_max = (N*(core-d))//(core*core-N*d)

    def mass(j):
        if group is None or j < group:
            return j*(errors+1)
        divisor = core+(j-1)*d
        covered = (j*core*core+divisor-1)//divisor
        return min(j*(errors+1), j*N-(j-1)*covered)

    worst = 0
    for j in range(min(v, rich_max)+1):
        heads = mass(j)
        check(heads <= budget, 'rich heads fit the budget')
        room = budget-heads
        m = a-j
        for total in range(j+1, v+1):
            rest = total-j
            check(rest*cutoff <= room, 'linear factors at the cutoff')
            worst = max(worst, heads+rest*cutoff)
            for b in range(2, rest+1):
                w = r*t-1-(total-b)*d
                if w < b*d or m < b:
                    price = cutoff
                else:
                    price = max(cutoff, tangent_cap(b, m, w, t, d))
                check(rest*price <= b*room, 'proportional price')
                if b == rest:
                    worst = max(worst, heads+price)
    check(worst <= budget, 'largest allocation')
    # Theorem D' needs characteristic above max(b, B_Z) for every factor
    check((2*v-2)*(r*t-1)+1 < 2**47, 'characteristic bound 2^47')
    return worst


def four_head_boundary(rate, errors):
    """One more error and four rich heads need not contain a collinear
    triple, so the head count used here no longer applies."""
    d = N//rate-1
    last, nxt = N-errors-255, N-errors-1-255
    check(4*last > N+4*d and not 4*nxt > N+4*d, 'four-head boundary')


ROWS = (
    # rate, beta, safe errors, first shape, second shape
    (2, 32, 307759023, (16, 22, 13629), (32, 45, 538)),
    (2, 34, 309134539, (20, 28, 37924), (39, 55, 842)),
    (2, 36, 310191320, (25, 35, 1789925), (51, 72, 1298)),
    (2, 38, 311064833, (32, 45, 40130), (63, 89, 2032)),
    (2, 40, 311753565, (40, 56, 259730), (80, 113, 3169)),
    (2, 44, 312769668, (64, 90, 612792), (128, 181, 7956)),
    (2, 48, 313401975, (102, 144, 622486), (203, 287, 19781)),
    (4, 32, 527124673, (14, 27, 8712), (27, 54, 541)),
    (4, 34, 529408947, (18, 35, 321384), (34, 68, 910)),
    (4, 36, 530904312, (22, 44, 1503703), (44, 88, 1408)),
    (4, 38, 532151237, (28, 56, 252397), (56, 112, 2231)),
    (4, 40, 533136284, (36, 71, 527625), (70, 140, 3539)),
    (4, 44, 534507592, (57, 113, 606978), (112, 224, 8751)),
    (4, 48, 535375373, (90, 179, 1934686), (178, 356, 21716)),
    (8, 32, 671088385, (6, 16, 335), (9, 26, 128)),
    (8, 34, 680837212, (9, 25, 520374), (17, 49, 356)),
    (8, 36, 687671509, (19, 53, 76589), (37, 106, 1436)),
    (8, 38, 688993288, (24, 67, 122992), (47, 134, 2251)),
    (8, 40, 690063301, (30, 85, 266338), (59, 168, 3567)),
    (8, 44, 691551680, (48, 135, 380311), (95, 270, 8805)),
    (8, 48, 692503565, (76, 215, 1421402), (152, 431, 22100)),
    (16, 32, 738197249, (2, 6, 102), (3, 13, 20)),
    (16, 34, 786379766, (5, 21, 56862), (10, 42, 179)),
    (16, 36, 798744899, (16, 62, 23006), (30, 122, 1337)),
    (16, 38, 800141773, (20, 78, 115580), (38, 154, 2130)),
    (16, 40, 801231080, (25, 99, 72982), (49, 198, 3385)),
    (16, 44, 802743393, (39, 157, 1471493), (78, 314, 8436)),
    (16, 48, 803694497, (63, 250, 2531324), (124, 498, 21133)),
)


DEEP_ROWS = (
    # larger shapes; checked only with --deep (about two minutes)
    (2, 52, 313793593, (159, 224, 60088785), (319, 451, 48072)),
    (2, 56, 314048997, (251, 355, 14656321), (400, 566, 127620)),
    (4, 52, 535924515, (142, 283, 10675868), (282, 564, 54011)),
    (4, 56, 536193245, (198, 396, 11806773), (394, 788, 105133)),
    (8, 52, 693095909, (120, 339, 28506938), (240, 680, 54927)),
    (8, 56, 693247147, (141, 399, 9680007), (282, 799, 75602)),
    (16, 52, 804286356, (99, 395, 4198332), (197, 790, 52469)),
)


if __name__ == '__main__':
    import sys
    rows = ROWS
    if '--deep' in sys.argv:
        rows = tuple(sorted(ROWS+DEEP_ROWS))
    previous = {}
    for rate, beta, errors, outer, secondary in rows:
        worst = certify(rate, beta, errors, outer, secondary)
        check(errors < JOHNSON_COUNT[rate], 'below the Johnson count')
        if rate in previous:
            check(errors >= previous[rate], 'monotone in the budget')
        previous[rate] = errors
        index = {2: 0, 4: 1, 8: 2, 16: 3}[rate]
        old = JOHNSON_LADDER.get(beta, (None,)*4)[index]
        gain = '' if old is None else f'; weighted Johnson ladder {old}'
        print(f'rate 1/{rate}, beta {beta}: safe through {errors} errors '
              f'with shapes {outer} and {secondary}; largest allocation '
              f'{worst} <= 2^{beta}{gain}')
    four_head_boundary(8, 671088385)
    four_head_boundary(16, 738197249)
    print(f'{CHECKS} explicit checks passed')
