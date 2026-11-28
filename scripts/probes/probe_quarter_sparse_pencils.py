"""Verify dyadic collision estimates for four- and five-frequency quarter-rate pencils."""
from collections import Counter
from itertools import combinations
from math import isqrt

from probe_monomial_power_graphs import P, generator, row_basis


def pair_bound(pair_budget):
    return (1+isqrt(1+4*pair_budget))//2


def trinomial_bound(n):
    return min(pair_bound(n-1), 2*max(1,n//128))


def one_minority_bound(n):
    return min(n,pair_bound((n-1)*trinomial_bound(n)))

def one_minority_any_field(n):
    return min(n,pair_bound((n-1)*pair_bound(n-1)))


def check_trinomial_control():
    n = 128
    assert 3**96 < 2**153 < P
    z = generator(n)
    points = [pow(z,j,P) for j in range(n)]
    inverse = [0]+[pow(y-1,-1,P) for y in points[1:]]
    maximum = 0
    for d in range(n):
        slopes = Counter((points[d*j%n]-1)*inverse[j]%P for j in range(1,n))
        slopes.pop(0,None)
        slopes.pop(1,None)
        maximum = max(maximum,1+max(slopes.values(),default=0))
    assert maximum==2


def check_64():
    n = 64
    z = generator(n)
    tested = maximum = 0
    for a,b,c in combinations(range(1,n//4),3):
        if not (a%2 or b%2 or c%2):
            continue
        freqs = (0,a,b,c)
        grid = [tuple(pow(z,j*f,P) for f in freqs) for j in range(n)]
        for t,u in combinations(range(1,2*n//11+1),2):
            basis = row_basis(grid[j] for j in (0,t,u))
            assert len(basis)==3
            free = next(j for j in range(4) if j not in basis)
            kernel = [1]*4
            for pivot,row in basis.items():
                kernel[pivot] = -row[free]
            if 0 in kernel:
                continue
            zeros = sum(sum(x*y for x,y in zip(kernel,row))%P==0 for row in grid)
            tested += 1
            maximum = max(maximum,zeros)
    assert maximum==9
    print(f'64 sites: {tested} full-support short-triple kernels, maximum {maximum} zeros in these kernels.')


def check_scales():
    for j in range(7,31):
        n = 1<<j
        limit = 5*n//32
        assert one_minority_bound(n)<=limit
        for i in range(1,j-2):
            g = 1<<i
            pair = pair_bound((n-g)*trinomial_bound(n)+(g-1)*g)
            coset = g+n//g-1
            if g==n//8:
                coset = min(coset,max(g+1,one_minority_bound(n)))
            assert min(pair,coset)<=limit,(n,g)
        if j>=23:
            four = one_minority_any_field(n)
            five = pair_bound((n-1)*four)
            for i in range(1,j-2):
                g = 1<<i
                pair = pair_bound((n-g)*four+(g-1)*(n//4-1))
                coset = g+(n//g-1)*one_minority_any_field(g)
                five = max(five,min(pair,coset))
            assert four<=five
            for i in range(1,j-2):
                g = 1<<i
                pair = pair_bound((n-g)*pair_bound(n-1)+(g-1)*g)
                coset = g+n//g-1
                if g==n//8:
                    coset = min(coset,max(g+1,four))
                assert min(pair,coset)<=five,(n,g)
            assert five<=limit
            if j==30:
                assert five==142_946_455
                print(f'Full primitive grid: any mixed-parity five-term polynomial has at most {five:,} zeros.')


if __name__=='__main__':
    check_trinomial_control()
    check_64()
    check_scales()
