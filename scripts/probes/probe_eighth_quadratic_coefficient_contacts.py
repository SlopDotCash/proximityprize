#!/usr/bin/env python3
"""Exact second-prime eighth-rate certificate from contacts of the V² coefficient."""
from fractions import Fraction as F

from probe_joint_list_contact_boards import adaptive_interval, linear
from probe_linear_contact_quotient import N, rank, require, slots
from probe_low_rate_named_adaptive_cofactors import curve_bound


# Hundredths, in the order mean, variance, slope variance, derivative,
# leading coefficient, then the ordinate derivatives below its leading degree.
ROWS = [
    [(-788,0,5000,0,419)],
    [(-1188,0,5000,0,329,301)],
    [(-1247,0,5000,0,1,297,858), (-535,0,1589,0,100,0,466)],
    [(-1298,0,5343,0,0,298,896,0), (-829,0,1455,0,137,291,380,0),
     (-461,1142,0,0,150,280,0,0)],
    [(-886,0,1376,0,174,263,380,0,0)],
]


def coefficient_order(j,o):
    return next(i for i in range(o+1) if j+i+min(i,2)>=o)


def dual_bias(a,max_order,s,u):
    """Maximize the site residual over every integer order and real occupancy."""
    m,b,j,v,top,*cs = u
    highest = None
    for o in range(max_order+1):
        quad = b+j+(j/3 if o<=1 else 0)
        lin = m-2*s*(b+j)+v*o+sum(c*coefficient_order(k,o) for k,c in enumerate(cs))
        const = o+m*s-(b+j)*s*s-top*coefficient_order(a,o)
        p = F(lin<0) if quad==0 else max(F(0),min(F(1),-lin/(2*quad)))
        value = const-p*lin-p*p*quad
        highest = value if highest is None else max(highest,value)
    return highest


def middle_weights(d,t,stock,degree,rows_by_degree=ROWS):
    r = 6000
    s,rate = F(t,N),F(d,N)
    retained = stock-2*degree**2
    require(retained>degree*((r*t-1)//(d-1)), 'ordinary secondary Bezout')
    variance = rate-s*s+(s-rate)/retained
    slope_variance = rate-s*s+(2*s-rate)/retained

    def limits(w,a):
        ell = F(w-2*(d-1),N)
        return (0,variance,slope_variance,s+F(w-d+1,N),ell-a*rate,
                *(ell-k*rate for k in range(a)))

    def surplus(w,h,mean):
        jump = rank(r,h-2)-rank(r-1,h-2)
        cost = rank(r,h)-rank(r,h-2)+jump*mean
        return slots(r*t,h,d)-slots(r*t-w,h-2,d)-N*cost

    worst = None
    hi = 6*d-2
    require((hi-2*(d-1))//d==len(rows_by_degree)-1, 'complete leading degrees')
    for a,rows in enumerate(rows_by_degree):
        lo = max(4*(d-1),(a+2)*d-2)
        ends = [lo+(hi-lo)*i//32 for i in range(33)]
        for left,right in zip(ends,ends[1:]):
            certified = False
            for row in rows:
                u = tuple(F(c,100) for c in row)
                require(len(u)==5+a and min(u[1:])>=0, 'valid dual weights')
                bias = dual_bias(a,right//(d-1)+2,s,u)
                def mean(w):
                    return bias+sum(value*weight for value,weight in zip(limits(w,a),u))
                for h in range(300,r+1,300):
                    margin = min(surplus(w,h,mean(w)) for w in (left,right))
                    if margin>0:
                        worst = margin if worst is None else min(worst,margin)
                        certified = True
                        break
                if certified:
                    break
            require(certified, f'leading degree {a} on [{left},{right}]')
    return worst.__floor__()


def verify():
    d = N//8-1
    t = (F(679,2000)*N).__ceil__()
    primary = 10*t
    b = (primary-1)//(d-1)
    stock = N//8
    primary_gain = slots(primary,4,d)-N*rank(10,4)
    require(primary_gain>0 and 4*stock+b<=2*N, 'primary and small groups')
    require(stock>b*((3000*t-1)//(d-1)), 'linear secondary Bezout')
    linear(d,t,primary,b,7,False)
    require(max(6+10*d,F(N-d,t-d))+3*stock+b<=2*N, 'linear list count')
    rows = [
        (2,3000,24900,'6.204','.229',10000,6*d-2),
        (3,1000,10200,'9.763','.166',4000,4*(d-1)),
        (4,1000,10200,'13.02','.166',4000,4*(d-1)),
    ]
    for v,h,lam,b2,j2,r,lo in rows:
        adaptive_interval(v,h,lam,b2,j2,d,t,b,stock,r,80,(lo,primary-1))
    margin = middle_weights(d,t,stock,b)
    for v in (2,3):
        require(curve_bound(3,v,d,t)+(4-v)*stock+b<=2*N,'low-degree count')
    require(N-t==709_206_474, 'closed safe radius')
    print(f'Second-prime eighth rate is safe through {N-t:,} errors. '
          f'Primary surplus {primary_gain:,}. Least middle surplus {margin:,}.')


if __name__=='__main__':
    verify()
