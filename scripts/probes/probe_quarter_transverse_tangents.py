#!/usr/bin/env python3
"""Check all residual degree allocations at 529,940,000 quarter-rate errors."""
from math import comb

from probe_quarter_core_weighted_jets import jet_rows
from probe_tangent_head_windows import N, surplus
from probe_tangent_polar_windows import branch_price


D = N//4 - 1
E = 529_940_000
T = N - E
C = T - 255
PRIMARY = (19, 38, 37_338)
COMPANION = (37, 74, 1_051)
RESIDUAL = (38, 70, 909)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ceil_div(num, den):
    return -(-num//den)


def rich_heads(j):
    if j < 3:
        return j*(E+1), 0
    a = j//2
    discrete = ceil_div(2*a*j*C-j*(j-1)*D, a*(a+1))
    cauchy = ceil_div(j*C*C, C+(j-1)*D)
    pop = min(j*(E+1), j*N-(j-1)*max(discrete, cauchy))
    gap = discrete + T-N-D
    require(gap > 0 and a*(a+1) <= j*(j-1), 'transverse degree cancellation')
    return pop, gap


def main():
    r, v, s = PRIMARY
    _, cv, cs = COMPANION
    rr, rv, rs = RESIDUAL
    cutoff = max(1+E//256, 1+s*cv+v*cs, 1+s*rv+v*rs)
    require(cutoff == 2_802_951 and T*T>N*D and 3*C>N+2*D, 'head and Johnson tests')
    require(D+cs*N//cutoff+3*(cs*N//(cutoff-cs)) < T, 'identity sites')
    ranks = [surplus(shape, T, D) for shape in (PRIMARY, COMPANION)]
    weight = rr*T - 6*D
    columns = sum((rs+1-i)*max(0,weight-i*D) for i in range(rv+1))
    loss = jet_rows(rr,rs) - jet_rows(rr-2,rs)
    correction = 4*(rs+1)
    for m in range(4):
        require(jet_rows(rr-2*m,rs)+m*loss <= jet_rows(rr,rs)+comb(m,2)*correction,
                'residual jet constraints')
    rows = N*jet_rows(rr,rs) - 3*C*loss + 3*D*correction
    ranks.append(columns-rows)
    require(ranks == [15_513_500, 5_182_964_995, 2_983_187_588], 'surface surpluses')

    worst = (0, ())
    checked = 0
    for j in range(v+1):
        pop, gap = rich_heads(j)
        m = min(cs-j, rs) if j >= 3 else cs-j
        degree, slope = (7,5) if j < 3 else (18,13) if j == 3 else (1,1)
        split = degree*(degree-1)
        for ell in range(j,v+1):
            rest = ell-j
            worst = max(worst, (s+pop, (j,ell,0)))
            for b in range(1,rest+1):
                w = r*T-1-(ell-b)*D
                price = cutoff
                if b >= 2 and b*D <= w and b <= m:
                    ordinary = branch_price(b,m,w,T,D,degree,slope,True,gap)
                    low = branch_price(b,min(m,split),w,T,D,1,1,True,gap) if b<=split else 0
                    price = max(cutoff, low, ordinary if split < m else 0)
                require(rest*price <= b*(2_146_244_663-s-pop), 'factor price')
                worst = max(worst, (s+pop+rest*price//b, (j,ell,b)))
                checked += 1
    require(worst == (2_146_244_663, (3,38,35)), ('maximum', worst))
    print('Rank surpluses', *ranks, 'and strict head cutoff', cutoff)
    print('Verified', checked, 'positive-degree inequalities. Maximum bad labels', worst[0], 'at', worst[1])


if __name__ == '__main__':
    main()
