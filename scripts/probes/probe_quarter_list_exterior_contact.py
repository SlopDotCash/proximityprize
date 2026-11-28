#!/usr/bin/env python3
"""Quarter-rate list certificate with the contact deficit of a word outside an equation."""
from fractions import Fraction
from math import isqrt

from probe_linear_contact_quotient import N, ORDER, rank, require, slots, upper_sqrt


def verify(extra=1_000_000, primary_order=7):
    d = N//4-1
    t = isqrt(N*d)-extra
    primary = primary_order*t
    degree = (primary-1)//(d-1)
    require(slots(primary,2,d)>N*rank(primary_order,2), 'primary')
    threshold = N//8
    retained = threshold-degree**2
    secondary = (ORDER*t-1)//(d-1)
    require(retained>degree*secondary, 'Bezout for every large group')
    s = Fraction(t,N)
    sigma = upper_sqrt(Fraction(d,N)-s*s+(s-Fraction(d,N))/retained)

    def surplus(v,h,w,mean):
        inc = rank(ORDER,h-v)-rank(ORDER-1,h-v)
        diff = slots(ORDER*t,h,d)-slots(ORDER*t-w,h-v,d)
        return diff-N*(rank(ORDER,h)-rank(ORDER,h-v)+inc*mean)

    def pieces(low,high,extra_cuts=()):
        cuts = {low,high+1}
        for j in range(low//d,high//d+2):
            cuts.update(z for z in (j*d-1,j*d) if low<z<=high)
        cuts.update(z for z in extra_cuts if low<z<=high)
        return zip(sorted(cuts), sorted(cuts)[1:])

    def best_row(v,left,stop,means):
        best = max(min(surplus(v,h,w,mean(w)) for w in (left,stop-1))
                   for mean in means for h in range(ORDER//10,9*ORDER//10+1,ORDER//20))
        require(best>0, f'weight interval {left}..{stop-1} at derivative degree {v}: {best}')
        return best.__floor__()

    quads = []
    for left,stop in pieces(2*(d-1),primary-1):
        def mean(w):
            return 1+Fraction(w-d+1,t)+(Fraction(w,d)+2)*sigma/(2*s)
        quads.append(best_row(2,left,stop,[mean]))

    def linear(outside):
        low = (5 if outside else 6)*d-1
        partitions = pieces(low,primary-1,(j*t for j in range(2,degree+2)))
        values = []
        for left,stop in partitions:
            a,b = (left-d+1)//d,left//d
            def bound(w,j):
                resultant = a*w+b*(w-d+1)-d*a*b
                saved = 2*max(j*t-w,0) if outside else 0
                return Fraction((j*(j+1)+1)*N+resultant-saved,2*j*N)
            values.append(best_row(1,left,stop,[lambda w,j=j: bound(w,j)
                                                for j in range(2,degree+2)]))
        return min(values)
    margins = min(quads), linear(False), linear(True)
    require((N-d)//(t-d)<threshold and 5+8*d<2*N, 'one group')
    require(4+6*d+threshold+degree<2*N, 'one large degree-four group')
    print(f'Quarter-rate safety through {N-t:,} errors for the 2n budget; '
          f'primary surplus {slots(primary,2,d)-N*rank(primary_order,2):,}.')
    print(f'Minimum quadratic, isolated linear and exterior-word surpluses: {margins}.')


if __name__ == '__main__':
    verify()
