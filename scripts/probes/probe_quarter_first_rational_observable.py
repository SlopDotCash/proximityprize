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


def shifted_hankel(height, alpha, prime):
    """Evaluate the shifted binomial Hankel determinant as a product in the field."""
    def rising_table(start, length):
        values = [1]
        for k in range(length):
            values.append(values[-1] * (start + k) % prime)
        return values

    factorial = rising_table(1, 2*height+1)
    first = rising_table(alpha, height+1)
    second = rising_table(1-alpha, height)
    numerator = denominator = 1
    for i in range(height+1):
        numerator = numerator * first[i+1] * factorial[i] * second[height-i] % prime
        denominator = denominator * factorial[height+i+1] % prime
    return numerator * pow(denominator, -1, prime) % prime


def check_hankel(height, prime):
    """Compare direct elimination with the product, then test all full-size exponents."""
    small = 101
    for h in range(6):
        for alpha in (pow(2, -1, small), 2*pow(3, -1, small), pow(4, -1, small)):
            moments = [1]
            for j in range(2*h+1):
                moments.append(moments[-1]*(alpha+j)*pow(j+1, -1, small) % small)
            rows = [moments[i+1:i+h+2] for i in range(h+1)]
            det = 1
            for k in range(h+1):
                pivot = rows[k][k]
                require(pivot != 0, 'leading Hankel minor')
                det = det * pivot % small
                for i in range(k+1,h+1):
                    scale = rows[i][k]*pow(pivot, -1, small)
                    rows[i] = [(v-scale*w) % small for v,w in zip(rows[i],rows[k])]
            require(det == shifted_hankel(h, alpha, small), 'direct Hankel determinant')
    for num, den in ((1,2), (2,3), (1,4)):
        residue = shifted_hankel(height, num*pow(den,-1,prime), prime)
        require(residue != 0, 'full-size Hankel coefficient')


def verify(extra, height_test, weightwise=False, *, rational_midpoint=False):
    """Check the quotient inequalities for one parameter choice."""
    if rational_midpoint:
        require(weightwise and not height_test, 'midpoint uses the per-weight logarithmic test')
    d = N//4-1
    t = 2*d-extra
    primary_order = 8 if rational_midpoint else 7
    P = primary_order*t
    primary_degree = (P-1)//(d-1)
    stock = 250_000 if weightwise else N//40
    if rational_midpoint:
        stock = 2_000_000
    group = N+1-stock-primary_degree
    s = F(t,N)
    require(fast_slots(P,2,d)>N*rank(primary_order,2), 'primary')
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
    quadratic_order = 50_000 if rational_midpoint else 6_000
    quadratic_caps = range(300, quadratic_order-299, 300)
    quadratic_cuts = [k*d//16 for k in range(32, 256)] if rational_midpoint else []
    for low,stop in intervals(2*(d-1),P-1,quadratic_cuts):
        def quadratic(w):
            variance_width = F(w+2,d) if rational_midpoint else F(w,d)+2
            return N*(1+F(w-d+1,t)+variance_width*sigma/(2*s))
        require(any(all(order_floor(2,quadratic_order,h,w)>quadratic(w) for w in (low,stop-1))
                    for h in quadratic_caps), 'quadratic product')
    require(stock-primary_degree**2 > primary_degree*((quadratic_order*t-1)//(d-1)),
            'quadratic Bezout')

    nonrad = (N*(primary_degree+2)*(1-s*s/(F(d,N)+(2*s-F(d,N))/group))).__floor__()
    low_weight = t+2*d-1-nonrad
    require(3+2*d+stock+primary_degree<=N, 'polynomial right hand side of degree at most three')
    require(2+2*d+stock+primary_degree<=N, 'total degree at most two')
    require(group > primary_degree*((6000*t-1)//(d-1)), 'linear Bezout on lower weights')

    def intersection(w,a,b):
        return a*w+b*(w-d+1)-d*a*b

    def mean_upper(w,a,b,j):
        return F(N*(j*(j+1)+1)+intersection(w,a,b),2*j)

    if rational_midpoint:
        require(N-nonrad>2*d, 'repeated quadratic content bound')
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
            comparisons = (0,2,3,4,5)
            if rational_midpoint and a == 2:
                comparisons += (-1,)
            def upper(w,j):
                if j == -1:
                    return N+2*(w-d+1)-2*d
                return special(w) if j==0 else mean_upper(w,a,b,j)
            require(any(all(order_floor(1,6000,h,w)>upper(w,j) for w in ends)
                        for j in comparisons for h in range(300,5800,300)),
                    f'lower linear interval at {low} for Y-degree {a}')

    r = 180_000_000 if rational_midpoint else 230_000_000
    exceptional_cap = r//2 if rational_midpoint else r//3
    high = 5*d+(4000 if height_test else 40*extra)
    require(group>(r*t-1)//d+5*exceptional_cap, 'mixed Bezout on the exceptional weights')
    H = exceptional = 0
    for low,stop in intervals(5*d-1,high):
        a,b = (low-d+1)//d,low//d
        for w in (low,stop-1):
            count = intersection(w,a,b)+10*N-5*order_floor(1,r,exceptional_cap,w)
            height = max(2*(w-3*d+1),w-d+1)-2*t+2*count
            H = max(H,height.__floor__())
            exceptional = max(exceptional,count.__floor__())
    require(high-d+1<2*(N-exceptional), 'constant denominator')
    require(high-2*d+1<N-exceptional, 'denominator of degree one or two')
    require(4*(t-exceptional-(high-5*d+1))>high-d+1, 'fourth power of a linear polynomial')
    prime = 365375409332725729550921208179070755120141565953
    require(prime > max(r*t+1, (2*H+2)*5+4), 'separable jets and Pade coefficients')
    require(F(N-d,t-d)<group, 'integral-family cap')
    if height_test:
        require((H+1)*(8*H+12)<group, 'Pade determinant root bound')
        check_hankel(H, prime)

    for low,stop in intervals(high+1,P-1,[5*d+d//16,5*d+d//4]):
        a,b = (low-d+1)//d,low//d
        rr = r if low<6*d-1 else 6000
        require(any(group>(rr*t-1)//d+h*b and
                    all(order_floor(1,rr,h,w)>mean_upper(w,a,b,j) for w in (low,stop-1))
                    for j in (2,3,4,5,6) for h in
                    (rr//5,rr//3,rr//2,2*rr//3,8*rr//10)), 'upper linear interval')
    if height_test:
        print(f'{N-t:,} safe errors; dominant population {group:,}; at most {nonrad:,} '
              f'nonradial sites and {exceptional:,} exceptional contact orders.')
        print(f'Rational height {H:,} gives at most {(H+1)*(8*H+12):,} polynomial sections.')
        return

    if weightwise:
        # For each weight, charge the discriminant and resultant simultaneously.
        # The order-six bound follows from D < 6d-1 and o <= D/d+1.
        require(high < 6*d-1, 'order and degree range of the harmonic quartic')
        invariant_orders = [0, 0, 1, 1, 3, 4, 6]
        for order, local in enumerate(invariant_orders):
            plane = max(0, order**2-order-1)
            charge = plane+local-int(order!=3 and plane+local>0)
            require(local-int(order!=3)>=order-2, 'lower bound on good sites')
            require(charge>=5*order-9, 'charge against logarithmic support')

            if rational_midpoint:
                midpoint_contact = min(order,3)-int(order==1)
                require(2*midpoint_contact >= 6*order-7-plane, 'midpoint contact with Hessian content')
        worst_support = worst_symmetry = None
        count = excluded = 0
        offsets = ([i*extra//8 for i in range(1,321)] if rational_midpoint else
                   [i*extra for i in range(2,41,2)])
        for low,stop in intervals(5*d-1, high, [5*d+x for x in offsets]):
            a,b = (low-d+1)//d,low//d
            bounds = []
            for w in (low, stop-1):
                ell = w-5*d+1
                z = order_floor(1,r,exceptional_cap,w)
                different = intersection(w,a,b)+10*N-5*z
                bounds.append((w,ell,z,different))
            if (all(different<0 for _,_,_,different in bounds) or
                    any(all(z>mean_upper(w,a,b,j) for w,_,z,_ in bounds) for j in (2,3,4))):
                excluded += 1
                continue
            count += 1
            for w,ell,z,different in bounds:
                e = 4*d+ell
                i_degree = 4*d+2*ell
                bad = i_degree+2*N-z
                good = N-bad
                symmetry = 3*good+3*(t-bad)-w-12*d-6*ell
                support = i_degree+ell+4*w+5*e-20*d+9*N-5*z
                if rational_midpoint:
                    symmetry = 3*z-F(7*N+intersection(w,a,b),2)-w-6*(d+ell)
                    support -= ell
                require(2*(N-different)>3*e-6*d, 'quartic invariant globally zero')
                require(3*(t-different-ell)>e, 'split quartic')
                require(6*(t-different)>2*e+d+ell, 'pure cubic')
                require(2*(t-bad)>3*d+ell, 'cubic central root')
                require(symmetry>0 and group>20, 'rational-section differential identity')
                require(8*(support+1)<group-1 and prime>2*support+2,
                        'finite support and numerator degree')
                worst_support = support if worst_support is None else max(worst_support,support)
                worst_symmetry = symmetry if worst_symmetry is None else min(symmetry,worst_symmetry)
        print(f'{N-t:,} safe errors; at most {worst_support.__floor__():,} logarithmic poles; '
              f'{group:,} required solutions.')
        identity = 'midpoint' if rational_midpoint else 'symmetry'
        print(f'{count} weight intervals checked for {identity} and support, {excluded} '
              f'excluded by the intersection bounds; {identity} surplus {worst_symmetry.__floor__():,}.')
        return

    slack = high-5*d+1
    invariant_i_degree = 4*d+2*slack
    bad = exceptional + invariant_i_degree - (N-exceptional)
    rational_excess = slack + extra + bad
    image_hits = N-bad-(2*d+slack)
    require(2*(N-exceptional)>6*d+3*slack, 'cubic quartic invariant vanishes')
    require(3*(t-exceptional-slack)>4*d+slack, 'quartic split into linear factors')
    require(6*(t-exceptional)>2*(4*d+slack)+(d+slack),
            'cubic pure power with content')
    require(2*(t-bad)>3*d+slack, 'cubic rational central root')
    require(3*image_hits>high+6*rational_excess, 'involuted rational sections')
    require(group>20, 'rational vector field identity')
    print(f'At {N-t:,} errors an over-budget list requires a squarefree harmonic quartic '
          f'denominator. Exceptional sites: at most {exceptional:,}.')
    print(f'At least {N-bad:,} sites have an ordinary triple root; involuted solutions '
          f'have at least {image_hits:,} hits, with weighted excess at most {rational_excess:,}.')


def verify_two_million():
    """Verify the midpoint/logarithmic certificate at two million beyond 2d."""
    verify(2_000_000, False, weightwise=True, rational_midpoint=True)


if __name__ == '__main__':
    verify(90, True)
    verify(100_000, False)
    verify(1_450_000, False, weightwise=True)
    verify_two_million()
