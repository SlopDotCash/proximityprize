#!/usr/bin/env python3
"""Half-rate allocation with tangent denominators bounded on the surface Gauss graph."""
from probe_tangent_head_windows import BUDGET, N, surplus

ERRORS = 312_250_000
T = N - ERRORS
D = N // 2 - 1
PRIMARY = (50, 70, 63_277)
COMPANION = (97, 137, 4_712)
BOUND = 2_131_191_599
CUTOFF = PRIMARY[2]*COMPANION[1] + PRIMARY[1]*COMPANION[2] + 1
CORE = T - ERRORS//CUTOFF


def check(test, message):
    if not test:
        raise ValueError(message)


def head_mass(j):
    if j < 3:
        return j*(ERRORS+1)
    denominator = CORE + (j-1)*D
    union = (j*CORE**2 + denominator-1)//denominator
    return min(j*(ERRORS+1), max(0, j*N - (j-1)*union))


def price(total, heads, degree):
    if degree == 1:
        return CUTOFF
    weight = PRIMARY[0]*T - 1 - (total-degree)*D
    m = COMPANION[2]-heads
    b = degree
    check(b*D <= weight and b <= m, 'component degree/weight')
    g = (2*b-2)*m - b*(b-1)
    height = (6*b+2)*weight*m
    loss = (g+m)*N
    fixed = min(2, heads)
    ordinary = (2*T*loss+N*(2*height+m*N))//(T*T-N*D)
    triangle = m*(m-1)+(3-fixed)*(loss+height)//(3*T-N-2*D-fixed*255)
    return max(CUTOFF, g+2*b*m+min(ordinary, triangle))


def run():
    surpluses = tuple(surplus(shape, T, D) for shape in (PRIMARY, COMPANION))
    check(min(surpluses) > 0, 'interpolants')
    m = COMPANION[2]
    check(CUTOFF >= ERRORS//256 + 1 and
          T - m*N//CUTOFF - 3*(m*N//(CUTOFF-m)) > D, 'rich affine extraction')
    check(3*CORE > N+2*D and T*T > N*D and 3*T > N+2*D+510, 'incidence gaps')
    check(2*PRIMARY[0]*T*PRIMARY[1] < 2**100, 'separable Gauss divisor projection')
    worst = (0, ())
    exact = 0
    for total in range(PRIMARY[1]+1):
        for heads in range(total+1):
            residual = total-heads
            base = head_mass(heads)+PRIMARY[2]
            prices = [0] + [price(total, heads, b) for b in range(1, residual+1)]
            worst = max(worst, (base, (heads, total, 0)))
            for b in range(1, residual+1):
                worst = max(worst, (base+residual*prices[b]//b, (heads, total, b)))
            best = [0]
            for size in range(1, residual+1):
                best.append(max(best[size-b]+prices[b] for b in range(1, size+1)))
            exact = max(exact, base+best[-1])
    check(exact == worst[0] == BOUND < BUDGET, 'factor partitions')
    print(f'Surpluses {surpluses}, cutoff {CUTOFF}, minimum core {CORE}.')
    print(f'{BOUND} labels at {ERRORS} errors, slack {BUDGET-BOUND}; '
          f'(heads, total degree, part)={worst[1]}.')


if __name__ == '__main__':
    run()
