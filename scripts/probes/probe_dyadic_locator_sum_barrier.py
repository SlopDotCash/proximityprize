#!/usr/bin/env python3
"""Check locator-fiber caps and explicit lists on the 237-bit Gaussian-period witness."""
from collections import Counter
from itertools import combinations
from math import comb


P = 126205134105047729256068842055334737587878534445324289139206048206460929
G = 50329493603183882829305332600678170099788838530533491465177960535524808
BUDGET = P // 2**128


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def squared_separation(p, r, d, w):
    """Ceiling of p^(2r/d), truncated above the squared diameter 4w."""
    target = p**(2*r)
    lo, hi = 1, 4*w+1
    while lo < hi:
        mid = (lo+hi)//2
        if mid**d >= target:
            hi = mid
        else:
            lo = mid+1
    return lo


def fiber_cap(p, n, t, a, shift):
    """Upper bound for t-subsets with fixed moments 1-shift through a-shift (zero omitted)."""
    require(n > 0 and n & (n-1) == 0 and 0 <= t <= n, 'dyadic domain and support size')
    u = min(t, n-t)
    best, classes, m, depth = comb(n,u), 1, n, 0
    while m >= 2:
        d, w = m//2, u>>depth
        step = 1<<depth
        # The modular determinant counts distinct primitive roots, also for negative indices.
        roots = {(j//step) % m for j in range(1-shift,a-shift+1)
                 if j % step == 0 and (j//step) % 2}
        distance = squared_separation(p, len(roots), d, w)
        if distance <= 2*w:
            break
        classes *= distance//(distance-2*w)
        best = min(best, classes*comb(d, min(d//2,w//2)))
        m, depth = d, depth+1
    return best


def direct_check():
    for p,n,g in ((17,8,2),(257,16,2)):
        require(pow(g,n//2,p) == p-1,'control order')
        orbit = [pow(g,i,p) for i in range(n)]
        for t in (n//4,n//2,n//2+1):
            for a in (1,3,5):
                for s in (0,a//2,a):
                    exponents = [j for j in range(1-s,a-s+1) if j]
                    rows = [[pow(x,j,p) for x in orbit] for j in exponents]
                    counts = Counter(tuple(sum(row[i] for i in subset)%p for row in rows)
                                     for subset in combinations(range(n),t))
                    require(max(counts.values()) <= fiber_cap(p,n,t,a,s), 'exhaustive moment-fiber bound')


def main():
    require(pow(G,512,P)==P-1 and (G+pow(G,17,P))%P == 1,'237-bit root relation')
    direct_check()
    for k,a,b,expected,shifted in ((512,21,24,59400885600,1620288010530347424),
                                    (256,19,20,631098000,82762210517011200),
                                    (128,17,18,3020640,2506193190592),
                                    (64,15,16,11436768,175363776)):
        require(comb(509,(k-2)//2)>BUDGET and BUDGET**2*(k-1)<P+1,'list and MCA budgets')
        require(fiber_cap(P,1024,k+a,a,0)==expected<BUDGET,'polynomial-center bound')
        require(max(fiber_cap(P,1024,k+b,b,s) for s in range(b+1))==shifted<BUDGET,
                'shifted-center bound')
        print(f'k={k}: monomial list >2^{comb(509,(k-2)//2).bit_length()-1}, '
              f'polynomial cap {expected} at t={k+a}, shifted cap {shifted} at t={k+b}')


if __name__ == '__main__':
    main()
