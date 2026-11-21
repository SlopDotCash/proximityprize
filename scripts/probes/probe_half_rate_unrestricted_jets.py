#!/usr/bin/env python3
"""Exact certificate for the half-rate successor bound using unrestricted jets."""
from fractions import Fraction


def capacity(total, weight, d):
    last = min(total, (weight-1)//d)
    if last < 0:
        return 0
    triangular = last*(last+1)//2
    squares = last*(last+1)*(2*last+1)//6
    result = (total+1)*((last+1)*weight-d*triangular)-weight*triangular+d*squares
    direct = sum((total-j+1)*(weight-j*d) for j in range(last+1))
    if result != direct:
        raise ArithmeticError('closed capacity formula')
    return result


def main():
    h, a = 2**28, 14078000
    n, d, t, e = 4*h, 2*h-1, 3*h-a, h+a
    m, mu, s = 58, 1712, 536797744
    weight, jets = mu*t, mu*(mu+1)//2
    last = (weight-1)//d
    base = sum((m-j+1)*(3*t-j*d) for j in range(5))-n*(6*(m+1)-4)
    if base != 42906080 or last != 2523:
        raise ArithmeticError('initial interpolant capacity')
    for b in (2,3,4):
        if b*s+m*last > 2*h*b:
            raise ArithmeticError('scalar resultant degree')
        margins=[]
        for w in (b*d,3*t-1):
            hessian=(6*b-2)*w-3*b*b*d
            orders=Fraction(hessian+3*b*(b-1)*n,6*b-5)
            codim=(mu-b+1)*orders+n*b*(b-1)//2
            margin=capacity(s,weight,d)-capacity(s-b,weight-w,d)-(s+1-m)*codim-m*n*jets
            if margin <= 0:
                raise ArithmeticError('auxiliary surplus')
            margins.append(margin.numerator//margin.denominator)
        print(f'b={b}, endpoint surplus floors {margins}')
    if t-Fraction(m*n,2*h)-3*Fraction(m*n,2*h-m)<=d or e+1>2*h:
        raise ArithmeticError('affine head reduction')
    print(f'good through {e}; first failing half-rate count at least {e+1} at n={n}')


if __name__=='__main__':
    main()
