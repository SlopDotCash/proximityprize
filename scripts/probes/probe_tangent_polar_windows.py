#!/usr/bin/env python3
"""Integer certificates for the tangent-polar determinant and three production windows."""
from dataclasses import dataclass
from math import comb

from probe_tangent_head_windows import BUDGET, N, surplus


@dataclass(frozen=True)
class Window:
    rate: int
    errors: int
    primary: tuple
    companion: tuple
    degree: int
    slope: int


WINDOWS = (
    Window(2, 309800000, (23,32,85457), (46,65,1093), 8,7),
    Window(4, 529350000, (18,35,27103), (34,68,896), 7,5),
    Window(8, 671088639, (6,16,335), (9,26,128), 4,2),
)


def branch_price(b, m, w, t, d, s, a, use_polar, line_gap=0):
    """Population bound on a single range of actual scalar/value degrees."""
    ax = (2*b-2)*w-b*(b-1)*d
    gz = (2*b-2)*m-b*(b-1)
    height = 2*ax*gz+2*w*m
    loss = (gz+m)*N
    population = (2*t*loss+N*(2*height+m*N))//(t*t-N*d)
    if use_polar:
        h = comb(s+2, 2)
        degree_sum = s*(s+1)*(s+2)//3
        gap = a*h*t-comb(a+2, 3)*N-degree_sum*d
        if gap <= 0:
            raise ValueError('the tangent determinant has no positive gap')
        population = min(population, s*m*(m-1)+h*(a*loss+s*height)//gap)
    if line_gap > 0:
        population = min(population, m*(m-1)+(height+loss)//line_gap)
    return gz+2*b*m+population


def component_price(b, m, w, t, d, s, a):
    """Uniform in the factor's actual total degree m0 <= m."""
    def price_at(bound, use_polar):
        return branch_price(b, bound, w, t, d, s, a, use_polar)

    split = s*(s-1)
    if s == 0 or m <= split:
        return price_at(m, False)
    low = price_at(split, False) if b <= split else 0
    return max(low,price_at(m, True))


def verify(window):
    e = window.errors
    t,d = N-e,N//window.rate-1
    r,v,primary_total = window.primary
    _,v2,m2 = window.companion
    cutoff = max(primary_total*v2+v*m2+1, 81920 if window.rate==8 else e//256+1)
    ranks = [surplus(shape,t,d) for shape in (window.primary,window.companion)]
    if min(ranks)<=0 or t*t<=N*d or t-m2*N//cutoff-3*(m2*N//(cutoff-m2))<=d:
        raise ValueError('interpolant or affine extraction failed')
    c = t-e//cutoff
    if window.rate != 8 and 3*c<=N+2*d:
        raise ValueError('three-head determinant failed')
    if window.rate == 8 and (cutoff<81920 or t!=402653185):
        raise ValueError('five-head inputs failed')

    def head_bound(j):
        denominator = c+(j-1)*d
        union = (j*c*c+denominator-1)//denominator if j else 0
        collinear = min(j*(e+1),j*N-(j-1)*union)
        if window.rate != 8:
            return j*(e+1) if j<3 else collinear
        if j<=3:
            return j*(e+1)
        if j==4:
            return max(collinear, 2125114027)
        if j==5:
            return max(collinear, 2058021547)
        return collinear

    worst=(0,())
    for j in range(v+1):
        for ell in range(j,v+1):
            rest=ell-j
            base=head_bound(j)+primary_total
            worst=max(worst,(base,(j,ell,0)))
            for b in range(1,rest+1):
                w=r*t-1-(ell-b)*d
                m=m2-j
                cost=cutoff
                if b>=2 and w>=b*d and m>=b:
                    cost=max(cost,component_price(b,m,w,t,d,window.degree,window.slope))
                worst=max(worst,(base+rest*cost//b,(j,ell,b)))
    if worst[0]>BUDGET:
        raise ValueError((window,worst))
    return cutoff,ranks,worst


if __name__=='__main__':
    for window in WINDOWS:
        cutoff,ranks,(count,degree_data)=verify(window)
        print(f'1/{window.rate} safe through {window.errors}; at most {count} labels, '
              f'{BUDGET-count} below budget; (rich, total degree, part)={degree_data}; '
              f'cutoff {cutoff}; surpluses {ranks}')
