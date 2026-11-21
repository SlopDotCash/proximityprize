"""Exact incidence comparisons for the second-prime rate-sixteenth bounds."""
from fractions import Fraction


N = 2**30
D = 2**26 - 1


def require(statement, label):
    if not statement:
        raise AssertionError(label)


def cubic(x):
    return x*(x-1)*(x-2)


def ceil_div(a, b):
    return (a+b-1)//b


def one_site_and_split():
    e = 647627101
    t = N-e
    total = 2*N+1
    seed_size = 172000000
    big_size = 350093427
    # Fix exactly this many witnesses at one common coordinate, then delete it.
    first = ceil_div(total*t, N)
    a = Fraction(first*(t-1), N-1)
    lower = (N-1)*cubic(a)/cubic(first)
    cap = 1+e//(t-(seed_size-1))
    upper = D-1+Fraction((cap-2)*(seed_size-1-D), first-2)
    require(first == 852229447 and cap == 3 and lower-upper > Fraction(11,100),
            'seed core after deleting one common coordinate')
    # Keep exactly this many points after removing the seed and at most two more lines.
    remaining = total-3*(e+1)
    a = Fraction(remaining*D, seed_size)
    b = Fraction(remaining*(t-D), N-seed_size)
    require(2 <= a < b and remaining == 204602343, 'ordered tangent slopes')
    lower2 = (seed_size*cubic(a)+(N-seed_size)*cubic(b))/cubic(remaining)
    cap2 = 1+e//(t-(big_size-1))
    upper2 = D+Fraction((cap2-2)*(big_size-1-D), remaining-2)
    require(cap2 == 9 and lower2-upper2 > 10827, 'split-incidence contradiction')
    require(N+6*D < t+3*big_size and 3*(e+1) < total, 'three cores cover and fit budget')
    print(f'last proved good e={e}, threshold floor={(e+1)}/{N}, '
          f'seed margin={float(lower-upper):.8f}, split margin={float(lower2-upper2):.3f}')


def slice_line(size, steps, coordinate_bound, agreement_bound):
    for _ in range(steps):
        size = ceil_div(size*(agreement_bound-D), coordinate_bound-D)
    return size


def rank_sixteen():
    r = (N-1)//3
    e = 2*r-1
    t = N-e
    total = 2*N+1
    big = 350457399
    cap = 1+e//(t-big+1)
    require(cap == 96, 'small-line occupancy')
    first = slice_line(total,15,N,t)
    seed = t-e//(first-1)
    require((first,seed) == (18,315806421), 'first moderate core')
    after_seed = slice_line(total-cap,15,N-seed,t-D)
    require(after_seed == 98 and t-e//(after_seed-1) >= big, 'first large core')
    # Here all previously selected lines have a large core.
    lower = [total-(e+1),total-2*(e+1),total-(3*N-2*(3*big-3*D)),
             total-(4*N-3*(4*big-6*D))]
    lines = []
    for i, size in enumerate(lower,1):
        j = min(i,2)
        outside = N-j*big+(j*(j-1)//2)*D
        line = slice_line(size,15,outside,t-j*D)
        require(line >= cap+1, 'distinct large core from the remainder')
        lines.append(line)
    require(3*big+t > N+5*D and 2*(4*big-N) > 9*D and 5*big > N+10*D,
            'noncollinear triple, four-head determinant and five-head contradictions')
    print(f'predecessor e={e}, excluded affine dimensions <=16, '
          f'first seed occupancy={first} second={after_seed}, subsequent={lines}')


def two_lines_at_predecessor():
    e = 715827881
    t = N-e
    big = 350457399
    m = 626349393
    z = t-e//185
    outside = N-2*z+D
    single = 2*(z-D)
    a = Fraction(m*2*D,single)
    b = Fraction(m*(t-2*D),outside)
    derivative = lambda u: 3*u*u-6*u+2
    intercept = lambda u: cubic(u)-u*derivative(u)
    cap = 1+e//(t-big+1)
    lower = (single*cubic(a)+outside*cubic(b))/cubic(m)
    upper = D+Fraction((cap-2)*(big-1-D), m-2)
    require(z == 354044604 and 2 <= a < b and derivative(b) >= 2*derivative(a),
            'three tangent slopes')
    require(intercept(b) <= 2*intercept(a) and lower-upper > 2200,
            'worst overlap at d and strict cubic comparison')
    print(f'at most one 186-point secant at e={e} in an overbudget family; '
          f'three-zone strict margin={float(lower-upper):.4f}')


if __name__ == '__main__':
    one_site_and_split()
    rank_sixteen()
    two_lines_at_predecessor()
