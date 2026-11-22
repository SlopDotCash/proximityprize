#!/usr/bin/env python3
"""Check the shared resultant and companion-degree count at quarter rate."""
from probe_tangent_head_windows import N, surplus


D = N//4 - 1
E = 533_150_000
T = N - E
MISS = 8192
C = T - MISS
PRIMARY = (36, 72, 75_769)
COMPANION = (71, 142, 3565)
BOUND = 2_128_352_044


def require(test, description):
    if not test:
        raise ValueError(description)


def ceil(numerator, denominator):
    require(denominator > 0, 'positive denominator')
    return -(-numerator//denominator)


def heads(j):
    if j < 3:
        return j*(E+1), 0
    a = j//2
    discrete = ceil(2*a*j*C-j*(j-1)*D, a*(a+1))
    cauchy = ceil(j*C*C, C+(j-1)*D)
    return min(j*(E+1), j*N-(j-1)*max(cauchy, discrete)), discrete+T-N-D


def charge(j, m, h, loss, gap):
    """Population beyond discarded labels for one fixed true plane degree."""
    if j >= 4:
        return m*(m-1) + (h+loss)//gap
    if m <= 12:
        p = min(2, j)
        return m*(m-1) + (3-p)*(h+loss)//(3*T-N-2*D-p*MISS)
    p = min(3, j)
    return 4*m*(m-1) + (15-p)*(3*loss+4*h)//(45*T-10*N-40*D-3*p*MISS)


def price(j, largest, high, gap):
    """Uniform rate per unit of true plane degree for one of its two ranges."""
    b = min(72-j, largest)
    w = 36*T-1-j*D
    h, loss = (6*b+2)*w, (2*b-1)*N
    if j >= 4:
        extra = largest-1 + ceil(h+loss, gap)
    elif high:
        p = min(3, j)
        extra = 4*(largest-1) + ceil((15-p)*(3*loss+4*h), 45*T-10*N-40*D-3*p*MISS)
    else:
        p = min(2, j)
        extra = largest-1 + ceil((3-p)*(h+loss), 3*T-N-2*D-p*MISS)
    return 4*b-2+extra


def main():
    require([surplus(q,T,D) for q in (PRIMARY,COMPANION)] == [15_151_548,14_490_855_831],
            'actual interpolation rank surpluses')
    require(N+2*D < 3*C and E//MISS < PRIMARY[2] and COMPANION[2] < PRIMARY[2],
            'large heads divide both surfaces and have the stated core')
    linear = 1+ceil(4*N,T-D)
    resultant = PRIMARY[1]*COMPANION[2]+PRIMARY[2]*COMPANION[1]
    require((linear,resultant) == (17,11_015_878), 'linear and noncommon budgets')
    worst = (0,0)
    trials = 0
    for j in range(PRIMARY[1]+1):
        mass, gap = heads(j)
        mmax = COMPANION[2]-j
        residual = PRIMARY[1]-j
        unit = 0
        if residual >= 2:
            unit = max(price(j,12,False,gap),price(j,mmax,True,gap))
            for m in range(2,mmax+1):
                b = min(residual,m)
                w = PRIMARY[0]*T-1-j*D
                g = (2*b-2)*m-b*(b-1)
                h = (6*b+2)*w*m
                loss = (g+m)*N
                actual = g+2*b*m+charge(j,m,h,loss,gap)
                require(actual <= unit*m, (j,b,m,actual))
                trials += 1
        total = mass+PRIMARY[2]+resultant+residual*PRIMARY[2]+linear*mmax+unit*mmax
        worst = max(worst,(total,j))
    require(worst == (BOUND,3) and BOUND < 2*N, 'all rich-head counts')
    print(f'{trials:,} actual plane-degree cases, 73 head counts; '
          f'maximum {BOUND:,} at three heads, slack {2*N-BOUND:,}.')


if __name__ == '__main__':
    main()
