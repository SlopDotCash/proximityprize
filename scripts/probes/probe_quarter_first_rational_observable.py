#!/usr/bin/env python3
"""Certify the first-prime quarter-rate quotient exclusions and rational-height bound."""
from fractions import Fraction as F

from probe_linear_contact_quotient import N, rank, require, slots, upper_sqrt


def moments(end):
    return end, end*(end-1)//2, end*(end-1)*(2*end-1)//6


def fast_slots(w,h,d):
    """Sum columns by the constant ceil((w+k)/d) on successive ranges of k."""
    if w<=0:
        return 0
    stop = min(h+1,(w-1)//(d-1)+1)
    pos,total = 0,0
    while pos<stop:
        top = (w+pos+d-1)//d
        end = min(stop,top*d-w+1)
        length,first,second = [b-a for a,b in zip(moments(pos),moments(end))]
        twice = (length*top*(2*w-d*(top-1))+first*(2*top-d-2*w)+second*(d-2))
        require(twice%2==0, 'integral column sum')
        total += twice//2
        pos = end
    return total


def verify():
    d = N//4-1
    t = 2*d-90
    P = 7*t
    primary_degree = (P-1)//(d-1)
    stock = N//40
    group = N+1-stock-primary_degree
    s = F(t,N)
    require(fast_slots(P,2,d)>N*rank(7,2), 'primary')
    for small_degree in (2,7,15):
        for w in range(-3,80):
            for h in (0,1,5,13,45):
                require(fast_slots(w,h,small_degree)==slots(w,h,small_degree),
                        'column sum versus explicit monomials')

    def intervals(low,high,more=()):
        cuts = {low,high+1}
        cuts.update(z for k in range(primary_degree+3) for z in (k*d-1,k*d)
                    if low<z<=high)
        cuts.update(z for z in more if low<z<=high)
        cuts = sorted(cuts)
        return zip(cuts,cuts[1:])

    def order_floor(v,r,h,w):
        source = fast_slots(r*t,h,d)-fast_slots(r*t-w,h-v,d)
        return F(source-N*(rank(r,h)-rank(r,h-v)),rank(r,h-v)-rank(r-1,h-v))

    sigma = upper_sqrt(F(d,N)-s*s+(s-F(d,N))/(stock-primary_degree**2))
    for low,stop in intervals(2*(d-1),P-1):
        def quadratic(w):
            return N*(1+F(w-d+1,t)+(F(w,d)+2)*sigma/(2*s))
        require(any(all(order_floor(2,6000,h,w)>quadratic(w) for w in (low,stop-1))
                    for h in range(300,5701,300)), 'quadratic product')
    require(stock-primary_degree**2 > primary_degree*((6000*t-1)//(d-1)), 'quadratic Bezout')

    nonrad = (N*(primary_degree+2)*(1-s*s/(F(d,N)+(2*s-F(d,N))/group))).__floor__()
    low_weight = t+2*d-1-nonrad
    require(3+2*d+stock+primary_degree<=N, 'polynomial right hand side of degree at most three')
    require(2+2*d+stock+primary_degree<=N, 'total degree at most two')
    require(group > primary_degree*((6000*t-1)//(d-1)), 'linear Bezout on lower weights')

    def intersection(w,a,b):
        return a*w+b*(w-d+1)-d*a*b

    def mean_upper(w,a,b,j):
        return F(N*(j*(j+1)+1)+intersection(w,a,b),2*j)

    for a in range(4):
        for low,stop in intervals(low_weight,5*d-2,[4*d+d//4,4*d+d//2]):
            if low-d+1<a*d or (a==0 and low<4*d-1):
                continue
            b = low//d
            def special(w):
                E = w-d+1
                if a==3:
                    return F((2*a-2)*E-a*(a-1)*d+3*N,2)
                if a==2:
                    return 2*N+F(E-2*d,3)+F(intersection(w,a,b)-N,6)
                return N+2*(E-d) if a==1 else N+E
            if a==3:
                require(stop-1-4*d+1+nonrad<N, 'repeated cubic denominator')
            for o in range(primary_degree+3):
                cost = max(0,o*o-o-1)
                phi = max(o-a-1,int(o>=a+1))
                if a==2:
                    require(6*o<=11+2*phi+cost, 'top quadratic coefficient charge')
                if a==1:
                    require(o<=1+2*phi, 'linear coefficient charge')
            ends = low,stop-1
            def upper(w,j):
                return special(w) if j==0 else mean_upper(w,a,b,j)
            require(any(all(order_floor(1,6000,h,w)>upper(w,j) for w in ends)
                        for j in (0,2,3,4,5) for h in range(300,5800,300)),
                    f'lower linear interval at {low} for Y-degree {a}')

    r = 230_000_000
    h = r//3
    high = 5*d+4000
    require(group>(r*t-1)//d+5*h, 'mixed Bezout on the exceptional weights')
    H = exceptional = 0
    for low,stop in intervals(5*d-1,high):
        a,b = (low-d+1)//d,low//d
        for w in (low,stop-1):
            count = intersection(w,a,b)+10*N-5*order_floor(1,r,h,w)
            height = max(2*(w-3*d+1),w-d+1)-2*t+2*count
            H = max(H,height.__floor__())
            exceptional = max(exceptional,count.__floor__())
    require(high-d+1<2*(N-exceptional), 'constant denominator')
    require(high-2*d+1<N-exceptional, 'denominator of degree one or two')
    require(4*(t-exceptional-(high-5*d+1))>high-d+1, 'fourth power of a linear polynomial')
    prime = 365375409332725729550921208179070755120141565953
    require(prime > max(r*t+1, (2*H+2)*5+4), 'separable jets and Pade coefficients')
    require(F(N-d,t-d)<group, 'integral-family cap')
    require((H+1)*(8*H+12)<group, 'Pade determinant root bound')

    for low,stop in intervals(high+1,P-1,[5*d+d//16,5*d+d//4]):
        a,b = (low-d+1)//d,low//d
        rr = r if low<6*d-1 else 6000
        require(any(group>(rr*t-1)//d+h*b and
                    all(order_floor(1,rr,h,w)>mean_upper(w,a,b,j) for w in (low,stop-1))
                    for j in (2,3,4,5,6) for h in
                    (rr//5,rr//3,rr//2,2*rr//3,8*rr//10)), 'upper linear interval')
    print(f'{N-t:,} safe errors; dominant population {group:,}; at most {nonrad:,} '
          f'nonradial sites and {exceptional:,} exceptional contact orders in the resonant interval.')
    print(f'Rational height {H:,} gives at most {(H+1)*(8*H+12):,} polynomial sections.')


if __name__ == '__main__':
    verify()
