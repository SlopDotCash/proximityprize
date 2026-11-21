#!/usr/bin/env python3
"""Exact certificates for three production MCA windows with tangent-head caps.

The allocation argument is the one of
docs/research/proximity-gap/weighted-hodge-windows.md: two mixed Hasse
interpolants, a cutoff above which a factor divides both, rich affine heads
with large joint cores, and a population cap for every nonlinear factor.  The
only change is the cap.  Here it is Theorem D' of
docs/research/proximity-gap/section-incidence-hodge-index.md,

    M <= B_X + floor((m n (2 t + n) + 2 C' (t + n)) / (t^2 - n d)),
    C' = 2 B_X B_Z + b (W (m - b) + m (W - b d)),

valid when t^2 > n d.  The script

  1. reproduces the three totals of probe_weighted_hodge_windows.py with the
     weighted cap, as a regression test of the allocation code;
  2. checks the dynamic programme over allocations against direct enumeration;
  3. certifies the three new windows and prints their worst allocations;
  4. checks that the eighth-rate window ends where four rich heads stop being
     forced collinear;
  5. reproduces the integer values of Theorem D' that the Lean file checks.

All arithmetic is exact.  Checks are explicit calls, so the script also runs
under `python3 -O`.
"""
from fractions import Fraction
from itertools import combinations_with_replacement

N = 2**30
BUDGET = 2*N
CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise SystemExit(f'CHECK FAILED: {message}')


def surplus(shape, t, d):
    """Monomials minus mixed jet conditions for multiplicity r, value degree
    at most v, total scalar/value degree at most s and weight below r*t."""
    r, v, s = shape
    cols = sum((s-j+1)*max(0, r*t-j*d) for j in range(v+1))
    rows = N*sum((r-j)*(s+1-j) for j in range(r))
    return cols-rows


def branch_degrees(b, m, w, d):
    return (2*b-2)*m-b*(b-1)+1, (2*b-2)*w-b*(b-1)*d+1


def tangent_cap(b, m, w, t, d):
    """Theorem D' for an irreducible factor of value degree b, total
    scalar/value degree at most m and weight at most w."""
    bx, bz = branch_degrees(b, m, w, d)
    check(bx > 0 and bz > 0 and t*t > N*d, 'hypotheses of Theorem D-prime')
    budget = 2*bx*bz+b*(w*(m-b)+m*(w-b*d))
    return bx+(m*N*(2*t+N)+2*budget*(t+N))//(t*t-N*d)


def weighted_cap(b, m, w, t, d, kappa):
    """Inequality (1) of weighted-hodge-windows.md."""
    bx, bz = branch_degrees(b, m, w, d)
    den = (5*kappa**4-4*kappa**5)*t-d
    check(bx > 0 and bz > 0 and den > 0, 'hypotheses of the weighted cap')
    cost = 2*kappa**5*b*(4*m*bx*bz+m*N+bx*bz)+(N-d)*(m+1)
    return bx+cost//den


class Window:
    def __init__(self, rate, errors, outer, secondary, kappa=None):
        self.rate, self.errors = rate, errors
        self.outer, self.secondary, self.kappa = outer, secondary, kappa
        self.d = N//rate-1
        self.t = N-errors
        r, v, s = outer
        _, va, a = secondary
        self.surpluses = (surplus(outer, self.t, self.d),
                          surplus(secondary, self.t, self.d))
        check(min(self.surpluses) > 0, 'nonzero interpolants')
        self.cutoff = max(errors//256+1, s*va+v*a+1)
        check(self.t-a*N//self.cutoff-3*(a*N//(self.cutoff-a)) > self.d,
              'affine-head test')
        self.core = self.t-255
        self.group = 3 if 3*self.core > N+2*self.d else 4
        check(self.group == 3 or 4*self.core > N+4*self.d,
              'rich-head determinant')

    def cap(self, b, j, degree):
        r, v, s = self.outer
        a = self.secondary[2]
        if b == 1:
            return self.cutoff
        w = r*self.t-1-(degree-b)*self.d
        m = a-j
        if w < b*self.d or m < b:
            return self.cutoff
        if self.kappa is None:
            value = tangent_cap(b, m, w, self.t, self.d)
        else:
            check(5 <= 2*self.kappa*(b+2), 'weighted moment sign')
            value = weighted_cap(b, m, w, self.t, self.d, self.kappa)
        return max(self.cutoff, value)

    def affine_mass(self, j):
        e = self.errors
        if j < self.group:
            return j*(e+1)
        divisor = self.core+(j-1)*self.d
        covered = (j*self.core*self.core+divisor-1)//divisor
        return min(j*(e+1), j*N-(j-1)*covered)

    def worst_by_enumeration(self):
        v = self.outer[1]
        worst = (-1, None)
        for j in range(v+1):
            for count in range(v-j+1):
                for degrees in combinations_with_replacement(
                        range(1, v-j+1), count):
                    degree = j+sum(degrees)
                    if degree > v:
                        continue
                    total = self.affine_mass(j)+sum(
                        self.cap(b, j, degree) for b in degrees)
                    worst = max(worst, (total, (j, degrees)))
        return worst

    def worst_by_dynamic_programme(self):
        """For fixed j and fixed total value degree the caps depend only on
        the part, so the best multiset is an unbounded knapsack."""
        v = self.outer[1]
        worst = (-1, None)
        for j in range(v+1):
            for degree in range(j, v+1):
                rest = degree-j
                caps = [0]+[self.cap(b, j, degree) for b in range(1, rest+1)]
                best = [0]*(rest+1)
                choice = [0]*(rest+1)
                for x in range(1, rest+1):
                    best[x], choice[x] = max(
                        (best[x-b]+caps[b], b) for b in range(1, x+1))
                parts = []
                x = rest
                while x > 0:
                    parts.append(choice[x])
                    x -= choice[x]
                total = self.affine_mass(j)+best[rest]
                worst = max(worst, (total, (j, tuple(sorted(parts)))))
        return worst


COMMITTED = (
    (Window(2, 299_100_000, (7, 9, 31973), (12, 17, 109), Fraction(912, 1000)),
     2128363411, 1266306256),
    (Window(4, 514_400_000, (6, 11, 6594), (11, 22, 110), Fraction(832, 1000)),
     1963198607, 1557879463),
    (Window(8, 665_600_000, (4, 12, 1729), (8, 24, 85), Fraction(757, 1000)),
     2137455396, 2020200012),
)

NEW = (
    (Window(2, 306_780_000, (14, 19, 238338), (27, 38, 412)),
     2140552088, (4, (15,))),
    (Window(4, 524_700_000, (11, 22, 2159), (21, 42, 353)),
     2145778288, (3, (19,))),
    (Window(8, 671_088_385, (6, 16, 335), (9, 26, 128)),
     2047343878, (3, (1,)*13)),
)


def regression():
    for window, weighted_total, tangent_total in COMMITTED:
        check(window.worst_by_enumeration()[0] == weighted_total,
              'committed weighted total')
        check(window.worst_by_dynamic_programme()[0] == weighted_total,
              'dynamic programme agrees with enumeration, weighted cap')
        same = Window(window.rate, window.errors, window.outer,
                      window.secondary)
        check(same.worst_by_enumeration()[0] == tangent_total,
              'tangent total on a committed window')
        check(same.worst_by_dynamic_programme()[0] == tangent_total,
              'dynamic programme agrees with enumeration, tangent cap')


def new_windows():
    rows = []
    for window, total, allocation in NEW:
        found = window.worst_by_dynamic_programme()
        check(found == (total, allocation), 'worst allocation of a new window')
        check(total <= BUDGET, 'production scalar budget')
        check(window.t*window.t > N*window.d, 'below the Johnson radius')
        rows.append((window, total, allocation))
    return rows


def eighth_rate_boundary():
    """One more error and four rich heads need not contain a collinear
    triple: the determinant test 4C > n + 4d fails."""
    d = N//8-1
    last, nxt = N-671_088_385-255, N-671_088_386-255
    check(not 3*last > N+2*d, 'three heads are not forced collinear')
    check(4*last > N+4*d and not 4*nxt > N+4*d, 'four-head boundary')


def lean_values():
    d, t = 2**26-1, 357913943
    def value(b, g, h, a, w, t, d):
        budget = 2*((2*b-2)*g+1)*((2*b-2)*a+1)+b*(w*(h-b)+h*(w-b*d))
        return (2*b-2)*g+(h*N*(2*t+N)+2*budget*(t+N))//(t*t-N*d)
    check(value(3, 34, 34, 290805098, 290805098, t, d) == 19433, 'cubic')
    check(value(4, 34, 34, 302954072, 302954072, t, d) == 41542, 'quartic')
    d, t = 2**28-1, N-480946858
    expected = (25522, 79953, 168073, 289882, 445379)
    for b, want in zip(range(2, 7), expected):
        check(value(b, 23, 23, 3*t-1, 3*t-1, t, d) == want,
              f'first-prime quarter-rate value, b={b}')


if __name__ == '__main__':
    regression()
    print('committed windows reproduced with both caps')
    for window, total, allocation in new_windows():
        j, degrees = allocation
        print(f'rate 1/{window.rate}: safe through {window.errors} errors; '
              f'shapes {window.outer} and {window.secondary}; '
              f'surpluses {window.surpluses}; cutoff {window.cutoff}; '
              f'worst total {total} <= {BUDGET} with {j} rich heads and '
              f'factor degrees {degrees}')
    eighth_rate_boundary()
    lean_values()
    print(f'{CHECKS} explicit checks passed')
