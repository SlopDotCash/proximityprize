#!/usr/bin/env python3
"""Verify the weighted fourth-mass anchor floor and the large-list contradiction."""
from fractions import Fraction as F
from math import isqrt

from probe_quarter_coset_lists import require
from probe_quarter_list_moving_jets import verify


def certificate():
    n = 2**30
    d = n//4-1
    m = 2*n+1
    t = 2*d-19
    r = n-2*t
    c = F(t-d,d)
    cap = 1/c
    L = 1+F(m*(n*d-t*t),n*(t-d))
    C = (L-1)*(L+1)**2
    Q = 2*L*C
    require(Q<m, 'second square mass moment')
    radicand = C*(m-1+L)
    R = isqrt(radicand.numerator//radicand.denominator)+1
    T = cap*(L*(L**2-1)+C+R)+cap**2*(R+L**2-1)
    h = 36_000_000
    mu = 1-F(h,d)
    tight = (c**4*(m-Q)-(c**6*T+2*m*c**2*(1-c*c))/(1-mu**2))/2
    require(tight>1_400_000 and L**2/mu**2<35_000, 'enough disjoint anchors')

    def square_edges(h):
        mu = 1-F(h,d)
        return (c*c*m-(Q+2*m*(1-c*c))/(1-mu**2))/2

    loose = square_edges(195_000_000)
    wide = square_edges(250_000_000)
    require(loose>343_000_000 and wide>394_000_000, 'loose edges')
    holes = r+h-1
    require(n-2*holes-(r+195_000_000-1)>3*d, 'first pencil determinant')
    require(n-8_000_000-(r+250_000_000-1)>3*d, 'ordinary-site pencil determinant')

    def johnson(e):
        w = F(e-4,2)
        return 1_400_000*((e-holes)**2-e*w)-e*(e-holes-w)

    max_e = 124_000_000
    require(johnson(max_e)>0 and johnson(max_e)>johnson(max_e-1), 'rational-center exceptional cap')
    require(1+3*max_e//2<343_000_000, 'negative Gram bound')
    require(160*(20_000+161) <= 81*(40_000-161), 'uniform dot product')
    for low, high, ceiling, size in [(20_000,500_000,124,343_000_000),
                                     (500_000,4_400_000,85,394_000_000)]:
        require(low>2*81**2 and F(82**2,81)/(1-F(81**2,low))<ceiling, 'positive cubic')
        require(ceiling*(high+161)<size, 'cubic list cap')
    low, middle = 4_400_000,85_000_000
    require(4*(middle+162)<343_000_000 and 4*81*F(low+1,low-81)<325, 'first trace subset')
    require(8*low>325*327**2, 'first trace rank')
    require((13*(max_e+162)+4)//5<323_000_000, 'second trace subset')
    require(81*F(13*(middle+1)+5,5*(middle-81))<212, 'second spectral radius')
    require(F(39,25)*middle>212*214**2, 'second trace rank')
    require(verify(n,20_000,343_000_000,82,83,16,4)[2:] == (7_998_800,17_150_000),
            'moving sections')
    print(f'{n-t:,} safe errors; {int(tight):,} tight, {int(loose):,} loose, {int(wide):,} small-exception pairs')


if __name__ == '__main__':
    certificate()
