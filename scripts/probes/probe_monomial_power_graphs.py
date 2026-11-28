"""Certify the small-subgroup power graphs and the remaining six-frequency first-prime code."""
from itertools import combinations
from math import gcd

from probe_low_degree_center_list_rigidity import PRIMES

P = PRIMES[0]


def generator(n):
    z = pow(3, (P-1)//n, P)
    assert pow(z,n//2,P) == P-1
    return z


def power_matches():
    n = 128
    z = generator(n)
    chart = [None]+[pow((pow(z,j,P)-1)%P,-1,P) for j in range(1,n)]
    maximum = 0
    for h in range(1,n//5+1):
        inverses = {j:pow((chart[j]-chart[h])%P,-1,P) for j in range(1,n) if j!=h}
        for d in range(n):
            second = h*d%n
            if not second:
                continue
            slopes = {}
            for j,inv in inverses.items():
                target = j*d%n
                if target in (0,second):
                    continue
                slope = (chart[target]-chart[second])*inv%P
                identity = slope==1 and chart[second]==chart[h]
                inversion = slope==P-1 and (chart[second]+chart[h]+1)%P==0
                if identity or inversion:
                    continue
                slopes[slope] = slopes.get(slope,0)+1
            maximum = max(maximum,2+max(slopes.values(),default=0))
    assert maximum==4
    print('Every non-scaling, non-reciprocal power graph has at most four matches on 128 sites.')


def row_basis(rows):
    """Reduced row echelon basis at the actual prime, including the pivot indices."""
    basis = {}
    for row in rows:
        row = list(row)
        for k in sorted(basis):
            factor = row[k]
            if factor:
                row = [(x-factor*y)%P for x,y in zip(row,basis[k])]
        pivot = next((j for j,x in enumerate(row) if x),None)
        if pivot is None:
            continue
        inverse = pow(row[pivot],-1,P)
        row = [x*inverse%P for x in row]
        for k,old in basis.items():
            if old[pivot]:
                basis[k] = [(x-old[pivot]*y)%P for x,y in zip(old,row)]
        basis[pivot] = row
    return basis


def six_frequencies():
    n = 64
    z = generator(n)
    freq = (1,13,35,14,36,48)
    rows = [tuple(pow(z,j*f,P) for f in freq) for j in range(n)]
    count = maximum = 0
    # Thirteen zeros have some cyclic block of five with span at most floor(4n/13).
    for other in combinations(range(1,4*n//13+1),4):
        basis = row_basis(rows[j] for j in (0,)+other)
        assert len(basis)==5
        free = next(j for j in range(6) if j not in basis)
        kernel = [0]*6
        kernel[free] = 1
        for pivot,row in basis.items():
            kernel[pivot] = -row[free]
        matches = sum(sum(x*y for x,y in zip(kernel,row))%P==0 for row in rows)
        maximum = max(maximum,matches)
        count += 1
    assert (count,maximum)==(3876,5)
    print(f'All {count} short five-row systems have rank five; maximum tested support {maximum}.')


def check_counts():
    for n in (512,1024,2048,4096):
        for g in (2**j for j in range(5,n.bit_length()-2)):
            cosets = n//g
            b = 4*max(1,g//128)
            assert g>3*b and gcd(n,g)==g
            bounds = (2*g+(cosets-2)*3*b+6, 2*g+6+(cosets-1)*2*b,
                      g+6+cosets*2*b, 2*g+(cosets-2)*3)
            assert all(16*x<=9*n for x in bounds), (n,g,bounds)
    assert 2*16+(512//16)*6 <= 9*512//16


if __name__ == '__main__':
    power_matches()
    six_frequencies()
    check_counts()
