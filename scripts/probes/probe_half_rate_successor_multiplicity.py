#!/usr/bin/env python3
"""Check the finite inequalities in the half-rate successor multiplicity argument."""

from fractions import Fraction


def main():
    h, s, cutoff, module_slack, slack = 2**28, 14, 10**6, 20652700, 23406000
    errors_beyond_unique = 1376592
    n, d, e, t = 4*h, 2*h-1, h+errors_beyond_unique, 3*h-errors_beyond_unique

    def surplus(r):
        variables = sum((r-j+1)*(3*t-j*d) for j in range(5))
        conditions = n*sum(r-j+1 for i in range(3) for j in range(3-i))
        value = variables - conditions
        a = errors_beyond_unique
        if value != (r+1)*(h+10-15*a)-14*h+30*a-30:
            raise ArithmeticError('monomial or jet count')
        return value

    margins = {
        'degree-14 interpolation': surplus(s),
        'rank lower bound': Fraction(surplus(cutoff), cutoff+1)-(h-module_slack),
        'agreement reserve': slack-module_slack-2*errors_beyond_unique,
        'quartic': 4*h-43*slack-132,
        'cubic two directions': 3*h-13*slack-70,
        'cubic fixed linear': 21*h-13*slack-40-3*(6*h+slack+1),
        'cubic fixed scalar': 34*h-13*slack-27-3*(8*h+slack),
        'quadratic three directions': 2*d-7*slack-45,
        'quadratic two linear directions': h-5*slack-17,
        'quadratic coprime directions': 2*(14*h-14*slack-64)-(22*h+2*slack+4),
        'quadratic common linear factor': 8*d-14*h-7*slack-33,
        'quadratic fixed scalar': 28*h-7*slack-12-3*(8*h+slack),
        'quadratic fixed linear': 21*h-7*slack-19-3*(6*h+slack+1),
        'quadratic two fixed lines': 14*h-7*slack-26-3*(4*h+slack+2),
        'quadratic fixed copy': 8*(4*h-slack-4)-(16*h+10*slack+32),
        'quadratic fixed distinct quadratic': 2*h-15*module_slack-14*errors_beyond_unique-38,
        'affine head secant': t-Fraction(14*n,14*cutoff)-3*Fraction(14*n,14*cutoff-14)-d,
        'four large heads required': n-3*(h+2)-14*cutoff,
        'large head core': h-5-(1+Fraction(h+1,2)),
        'noncollinear core determinant': 3*(3*h-2)-2*d-n,
        'two uncovered sites': 3*(n-2)-4*(3*h-2),
        'one uncovered site, degree two': 3*(n-1)-4*(3*h-2),
        'second named budget': 2*n-4*(e+1),
    }
    for i in range(4):
        if i*(3*i-2) < 21-13*(2*max(2-i,0)+(i<3)):
            raise ArithmeticError('cubic site deficit')
    for i, want in enumerate([8,4,1]):
        if min(4*a+max(3-i-a,0)**2 for a in range(4)) != want:
            raise ArithmeticError('quadratic horizontal resultant contribution')
    for name,value in margins.items():
        if value <= 0:
            raise ArithmeticError(f'{name}: {value}')
    print(f'{len(margins)} strict margins passed. rank ≥ {h-module_slack}, labels at the first successor ≤ {n+3}.')
    print(f'Second-prime first failing count ≥ {e+1} at n={n}; bad-label cap {4*(e+1)}.')


if __name__ == '__main__':
    main()
