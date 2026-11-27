"""Check homogeneous discriminant coranks and the quarter-rate parameter counts."""
from fractions import Fraction
from itertools import product
from probe_quarter_coset_lists import poly_mul, require
from probe_quarter_sixteen_splines import nullspace


def trim(poly, p):
    coeff = [x % p for x in poly]
    while coeff and not coeff[-1]:
        coeff.pop()
    return coeff


def monic_gcd(left, right, p):
    a, b = trim(left, p), trim(right, p)
    while b:
        inv = pow(b[-1], -1, p)
        while len(a) >= len(b):
            offset = len(a) - len(b)
            scale = a[-1] * inv
            for j, c in enumerate(b):
                a[offset+j] -= scale*c
            a = trim(a, p)
        a, b = b, a
    return a


def square(poly, p):
    coeff = trim(poly, p)
    if not coeff or len(coeff) % 2 == 0:
        return False
    # Geometric square test: divide by the leading coefficient, then use the
    # unique monic square root of the top half and verify all coefficients.
    coeff = [c * pow(coeff[-1], -1, p) % p for c in coeff]
    m = len(coeff)//2
    root = [0]*m+[1]
    for j in reversed(range(m)):
        known = sum(root[i]*root[m+j-i] for i in range(j+1, m))
        root[j] = (coeff[m+j]-known) * pow(2, -1, p) % p
    return poly_mul(root, root, p) == coeff


def board():
    p, d, ell = 23, 5, 1
    s = 2*d-1
    good, singular = set(), set()
    for a, b in product(range(p), repeat=2):
        # A=1, B=X^(2d-ell), S0=3 and P0=2. The fixed product is squarefree.
        J = [0]*(2*d+1)
        low = poly_mul([3+a, b], [3+a, b], p)
        J[:len(low)] = low
        J[0] -= 8
        J[2*d-ell] -= 4*a
        J[2*d-ell+1] -= 4*b
        degree = len(trim(J, p))-1
        dx = [i*J[i] % p for i in range(1, 2*d+1)]
        dz = [(2*d-i)*J[i] % p for i in range(2*d)]
        excess = len(monic_gcd(J, dx, p))-1 + max(0, 2*d-degree-1)
        cols = [[0]*shift + grad + [0]*(s-shift-1)
                for grad in (dx, dz) for shift in range(s)]
        corank = len(nullspace([list(row) for row in zip(*cols)], p))
        require(corank == excess, 'projective gradient corank')
        if square(J, p):
            good.add((a, b))
            require(corank >= d, 'corank at a geometric square')
        if excess > ell:
            singular.add((a, b))
    require((0, 0) in good, 'known split member')
    lines = [{(x, (c*x+e) % p) for x in range(p)} for c, e in product(range(p), repeat=2)]
    lines += [{(a, y) for y in range(p)} for a in range(p)]
    require(all(not line <= singular for line in lines), 'exceptional locus contains a tested line')
    print(f'Checked {p*p} homogeneous gradient coranks and {len(lines)} lines over F_{p}.')


if __name__ == '__main__':
    board()
    degree = 2**28 - 1
    ratio = Fraction(8*degree-6156, degree-3076)
    caps = [int(ratio**i) for i in (1, 2, 3, 9, 10)]
    require(caps == [8, 64, 512, 134228107, 1073834088], 'production dimensions')
    require(caps[-2] < 1072766345 <= caps[-1], 'forced dimension')
    print(f'The nine-dimensional cap is {caps[-2]:,}. The forced affine dimension is at least ten.')
