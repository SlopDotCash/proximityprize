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

A second table gives the same statement at integer budgets 9n/8, ..., 15n/8,
between the budgets n and 2n of the two named primes, and a third at length
2**40 with budgets 2n and 64n.  The caps are numbers that do not grow with the
length, so at the larger length the same budgets relative to n reach closer
to the Johnson count.

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


def surplus(shape, t, d, n=N):
    r, v, s = shape
    cols = sum((s-j+1)*max(0, r*t-j*d) for j in range(v+1))
    rows = n*sum((r-j)*(s+1-j) for j in range(r))
    return cols-rows


def tangent_cap(b, m, w, t, d, n=N):
    bx = (2*b-2)*m-b*(b-1)+1
    bz = (2*b-2)*w-b*(b-1)*d+1
    budget = 2*bx*bz+b*(w*(m-b)+m*(w-b*d))
    return bx+(m*n*(2*t+n)+2*budget*(t+n))//(t*t-n*d)


def certify(rate, budget, errors, outer, secondary, n=N):
    """Return the largest allocation total found by the price test."""
    d = n//rate-1
    t = n-errors
    r, v, s = outer
    _, va, a = secondary
    check(t*t > n*d, 'below the Johnson radius')
    check(surplus(outer, t, d, n) > 0 and surplus(secondary, t, d, n) > 0,
          'nonzero interpolants')
    cutoff = max(errors//256+1, s*va+v*a+1)
    check(t-a*n//cutoff-3*(a*n//(cutoff-a)) > d, 'affine-head test')
    core = t-255
    check(core*core > n*d, 'rich cores are above the Johnson size')
    if 3*core > n+2*d:
        group = 3
    elif 4*core > n+4*d:
        group = 4
    else:
        group = None
    rich_max = (n*(core-d))//(core*core-n*d)

    def mass(j):
        if group is None or j < group:
            return j*(errors+1)
        divisor = core+(j-1)*d
        covered = (j*core*core+divisor-1)//divisor
        # the union of j cores also has at least j C - binom(j, 2) d sites
        covered = min(n, max(covered, j*core-(j*(j-1)//2)*d))
        return min(j*(errors+1), j*n-(j-1)*covered)

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
                    price = max(cutoff, tangent_cap(b, m, w, t, d, n))
                check(rest*price <= b*room, 'proportional price')
                if b == rest:
                    worst = max(worst, heads+price)
    check(worst <= budget, 'largest allocation')
    # Theorem D' needs characteristic above max(b, B_Z) for every factor
    check((2*v-2)*(r*t-1)+1 < 2**47*(n//N), 'characteristic bound')
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


EIGHTH = N//8

BUDGET_ROWS = (
    # rate, integer budget, safe errors, first shape, second shape:
    # budgets between the two named ones, 2**30 and 2**31
    (2, 9*EIGHTH, 293018651, (5, 7, 140), (8, 11, 58)),
    (2, 10*EIGHTH, 302936496, (10, 13, 49960), (17, 24, 188)),
    (2, 11*EIGHTH, 305038412, (11, 15, 340818), (22, 31, 277)),
    (2, 12*EIGHTH, 305705113, (12, 17, 51353), (24, 34, 320)),
    (2, 13*EIGHTH, 305940243, (13, 18, 1396), (24, 34, 338)),
    (2, 14*EIGHTH, 306465090, (13, 18, 95004), (27, 38, 382)),
    (4, 9*EIGHTH, 469749153, (2, 3, 23419), (3, 6, 15)),
    (4, 10*EIGHTH, 488619120, (3, 5, 115), (5, 10, 27)),
    (4, 11*EIGHTH, 504801583, (4, 8, 203), (7, 14, 57)),
    (4, 12*EIGHTH, 518960616, (7, 14, 49036), (14, 28, 169)),
    (4, 13*EIGHTH, 522404939, (9, 18, 2657), (17, 34, 253)),
    (4, 14*EIGHTH, 523490200, (10, 20, 1655), (19, 38, 294)),
    (4, 15*EIGHTH, 524083702, (10, 20, 215373), (20, 40, 321)),
    (8, 9*EIGHTH, 601620356, (2, 4, 27), (2, 6, 11)),
    (8, 10*EIGHTH, 625533909, (2, 5, 34), (3, 9, 18)),
)


N40 = 2**40

LENGTH40_ROWS = (
    # length 2**40: rate, log2(budget / n), safe errors, first shape, second shape
    (2, 1, 319230068958, (40, 56, 156913), (80, 113, 3156)),
    (2, 6, 320634784370, (81, 114, 372525), (162, 229, 12508)),
    (4, 1, 545382552916, (31, 62, 289769), (62, 124, 2716)),
    (4, 6, 547825429161, (71, 142, 808376), (141, 282, 13706)),
    (8, 1, 687188686354, (5, 14, 120547), (10, 29, 126)),
    (8, 6, 707216801511, (35, 99, 894889), (70, 199, 4832)),
    (16, 1, 731100741633, (2, 5, 67), (2, 9, 12)),
    (16, 6, 819792658433, (21, 85, 350327), (42, 170, 2531)),
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
        worst = certify(rate, 2**beta, errors, outer, secondary)
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
    last = {}
    for rate, budget, errors, outer, secondary in BUDGET_ROWS:
        worst = certify(rate, budget, errors, outer, secondary)
        check(N < budget < 2*N, 'between the two named budgets')
        check(errors >= last.get(rate, 0), 'monotone in the budget')
        last[rate] = errors
        print(f'rate 1/{rate}, budget {budget} = {budget*8//N}n/8: safe through '
              f'{errors} errors with shapes {outer} and {secondary}; largest '
              f'allocation {worst}')
    for rate, kappa, errors, outer, secondary in LENGTH40_ROWS:
        worst = certify(rate, N40*2**kappa, errors, outer, secondary, N40)
        print(f'length 2^40, rate 1/{rate}, budget 2^{kappa} n: safe through '
              f'{errors} errors, {errors/N40:.5f} n; largest allocation {worst}')
    four_head_boundary(8, 671088385)
    four_head_boundary(16, 738197249)
    print(f'{CHECKS} explicit checks passed')
