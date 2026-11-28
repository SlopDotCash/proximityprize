"""Check dyadic compression cutoffs and translated power/projectivity matches."""
from itertools import product
from math import isqrt


def check_bounds():
    for exponent in range(13, 31):
        n = 2**exponent
        m = n//4
        # Rounding each square-root bound upwards also certifies the real bound.
        b = 2+isqrt(2*m)
        assert 2*15**3 < n
        assert 16*(15*(m+4)+6*(3*m-4)) < 9*n*15
        for upper in (2*m+6+3*(2+isqrt(2*n)), 2*m+6*b+6, m+8*b+6):
            assert 16*upper < 9*n, (exponent, upper)
        assert 3*b < m


def check_projectivities():
    p = 17
    grid = tuple(range(1,p))
    checked = 0
    for a,b,c,d in product(range(p), repeat=4):
        entries = (a,b,c,d)
        if next((x for x in entries if x),0) != 1 or (a*d-b*c)%p == 0:
            continue
        if (b==0 and c==0) or (a==0 and d==0):
            continue
        values = {x:(a*x+b)*pow((c*x+d)%p,-1,p)%p for x in grid if (c*x+d)%p}
        for power in range(16):
            matches = [x for x,y in values.items() if pow(x,power,p)==y]
            assert len(matches)*(len(matches)-1) <= 2*(len(grid)-1)
        checked += 1
    assert checked == 4864, checked
    print(f'{checked} projectivities at all sixteen powers; all 18 dyadic cutoffs pass.')


if __name__ == '__main__':
    check_bounds()
    check_projectivities()
