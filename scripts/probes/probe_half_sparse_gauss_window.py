#!/usr/bin/env python3
"""Check the sparse surface polar and the residual degree allocation at half rate."""
from math import comb
from probe_tangent_head_windows import BUDGET, N, surplus

E = 312_800_000
T = N-E
D = N//2-1
C = T-8192
PRIMARY = (66, 93, 123_104)
COMPANION = (128, 181, 8_245)
H = PRIMARY[2]
LINEAR = 1 + (4*N + T-D-1)//(T-D)


def check(value, message):
    if not value:
        raise ValueError(message)


def ceil_div(x, y):
    check(y > 0, 'positive divisor')
    return (x+y-1)//y


def union(j):
    a = 7*j//10
    return ceil_div(2*a*j*C-j*(j-1)*D, a*(a+1))


def head_mass(j):
    if j < 3:
        return j*(E+1)
    cover = max(union(j), ceil_div(j*C*C, C+(j-1)*D))
    return min(j*(E+1), max(0, j*N-(j-1)*cover))


def unit(j, b):
    w = PRIMARY[0]*T-1-j*D
    check(2 <= b <= PRIMARY[1]-j and b*D <= w, 'weight')
    height = (6*b+2)*w-3*b*b*D
    loss = (2*b-1)*N
    fixed = min(j, 2)
    triangle = 2*b+ceil_div((3-fixed)*(height+loss), 3*T-N-2*D-fixed*8192)
    price = triangle
    if j == 0:
        for s, a in ((6, 5), (8, 7)):
            if b <= s*(s-1):
                continue
            h = comb(s+2, 2)
            gap = a*h*T-comb(a+2, 3)*N-s*(s+1)*(s+2)//3*D
            price = min(price, 2*s*b+ceil_div(h*(a*loss+s*height), gap))
    if j >= 3:
        gap = T+union(j)-N-D
        price = min(price, 2*b+ceil_div(height+loss, gap))
    return 4*b-2+price


def run():
    sr = [surplus(shape, T, D) for shape in (PRIMARY, COMPANION)]
    check(min(sr) > 0 and max(1+E//8192, COMPANION[2]) <= H, 'interpolation and extraction')
    check(3*C > N+2*D and 4*N <= (LINEAR-1)*(T-D), 'core and identity tests')
    resultant = PRIMARY[1]*COMPANION[2]+PRIMARY[2]*COMPANION[1]
    worst = (0, ())
    for j in range(PRIMARY[1]+1):
        other = head_mass(j)+PRIMARY[2]+resultant+(PRIMARY[1]-j)*H+(COMPANION[2]-j)*LINEAR
        local, b = max(((unit(j, b), b) for b in range(2, PRIMARY[1]-j+1)), default=(0, 0))
        worst = max(worst, (other+(COMPANION[2]-j)*local, (j, b, local)))
    check(worst == (2_115_023_520, (0, 93, 252302)) and worst[0] < BUDGET, 'production budget')
    print(f'Surpluses {sr}, resultant {resultant}, small-head cutoff {H}, linear unit {LINEAR}.')
    print(f'Bound {worst[0]}, slack {BUDGET-worst[0]}, (heads, value degree, unit)={worst[1]}.')


if __name__ == '__main__':
    run()
