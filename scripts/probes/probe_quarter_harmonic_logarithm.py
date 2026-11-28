#!/usr/bin/env python3
"""Check the first-prime quarter logarithmic bound and its local multiplicity argument."""

from fractions import Fraction

from probe_linear_contact_quotient import N, rank, require
from probe_quarter_first_rational_observable import fast_slots, verify

PRIME = 365375409332725729550921208179070755120141565953


def valuation(polynomial):
    return next(i for i, value in enumerate(polynomial) if value)


def add(*polynomials):
    return [sum(poly[i] for poly in polynomials if i < len(poly))
            for i in range(max(map(len, polynomials)))]


def multiply(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def local_controls():
    # B(U,S) = US + S^3 + S^4. The solution f=v U^2 forces contact
    # with both factors in A+f'B=(S-vU²)(-S+wU²).
    for v in range(1, 9):
        for w in range(-8, 0):
            lengths = []
            for k in (v, w):
                section = [0, 0, k]
                square = multiply(section, section)
                b = add(multiply([0, 1], section), multiply(square, section),
                        multiply(square, square))
                lengths.append(valuation(b))
            require(sum(lengths) == 6, 'forced special slope increases intersection length')
    # In contrast B=S(U+S²), A=U³-S² have lengths 3 and 2
    # along the two irreducible components of B.
    along_s_zero = [0, 0, 0, 1]
    along_u_eq_minus_s2 = add([0, 0, -1], [0]*6 + [-1])
    require(valuation(along_s_zero) + valuation(along_u_eq_minus_s2) == 5,
            'the clean ordinary contact length is attainable')
    # At a good site c is the first-order coefficient of b₁.  Compute
    # Hessian at S=0, for b₀=A U², b₁=cU+O(U²), b₂=B U.
    for c in range(-3, 4):
        for a in (1, 2, 5):
            for b in (2, 4):
                b0, b1, b2 = [0, 0, a], [0, c, 1], [0, b]
                h = add([8*x for x in multiply(b0, b2)],
                        [-3*x for x in multiply(b1, b1)])
                require((valuation(h) == 2) == (c != 0), 'simple discriminant slope test')


def main():
    extra = 100_000
    # This also checks all factor-weight intervals and the harmonic reduction
    # at the same input. Recompute its exceptional-site bounds independently.
    verify(extra, False)
    d = N//4-1
    t = 2*d-extra
    high = 5*d+40*extra
    slack = high-5*d+1
    E = high-d+1
    M = N+1-N//40-(7*t-1)//(d-1)
    r = 230_000_000
    h = r//3

    def baseline_intersection(weight):
        a, b = (weight-d+1)//d, weight//d
        return a*weight+b*(weight-d+1)-d*a*b

    def exceptional_at(weight):
        columns = fast_slots(r*t, h, d)-fast_slots(r*t-weight, h-1, d)
        order = Fraction(columns-N*(rank(r, h)-rank(r, h-1)), rank(r, h-1)-rank(r-1, h-1))
        result = baseline_intersection(weight)+10*N-5*order
        return result.__floor__()

    # The interval has just one internal degree-cap change, at 5d.
    T = max(exceptional_at(w) for w in (5*d-1, 5*d, high))
    invariant_degree = 4*d+2*slack
    good = 2*N-invariant_degree-2*T
    intersection = 4*high+5*E-20*d
    remaining = intersection-5*(N-T)
    bad = N-good + invariant_degree-good + slack+remaining
    bound = 8*(bad+1)
    require((T, good, remaining, bad, bound) ==
            (5999835, 1053742156, 65999160, 117998495, 943987968),
            'intersection and pole counts')
    require(bound < M-1 == 1046898266, 'too many polynomial roots of the last derivative')
    require(max(2*bad+2, 2*d+slack) < PRIME, 'pole and derivative orders are nonzero')
    require(N-t == 536970914, 'closed error endpoint')
    local_controls()
    print(f'Exceptional abscissas at most {bad:,}; ordinate degree at most {bound:,}.')
    print(f'At least {M-1:,} distinct surviving sections would be required.')
    print(f'First-prime quarter rate safe through {N-t:,} errors.')


if __name__ == '__main__':
    main()
