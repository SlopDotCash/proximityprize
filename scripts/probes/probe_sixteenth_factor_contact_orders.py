#!/usr/bin/env python3
"""Certify both sixteenth-rate list budgets using declining site contact orders."""
from fractions import Fraction as F

from probe_eighth_quadratic_coefficient_contacts import middle_weights
from probe_joint_list_contact_boards import linear
from probe_linear_contact_quotient import N, rank, require, slots
from probe_low_rate_named_adaptive_cofactors import curve_bound


COEFFICIENT_ROWS = [
    [(-652,0,5000,0,314)],
    [(-974,0,5000,0,206,427)],
    [(-1057,0,5000,0,80,415,820),(-765,0,3593,0,97,14,699)],
    [(-1231,0,5000,0,107,464,745,0)],
    [(-1213,0,3993,0,174,449,648,0,0)],
]

# (secondary derivative cap, decline in the site multiplicity per order of g).
BOARDS = {
    2: [(795,300),(825,307),(810,303),(870,262),(945,270),(1125,284),
        (1410,247),(1710,217),(1935,191),(2055,169),(2145,151),(2280,125)],
    3: [(810,269),(825,240),(945,199),(1335,191),(1920,160),(2190,121)],
    4: [(870,227),(885,188),(930,174),(1005,162),(1665,148),(2040,116)],
}


def smooth_slots(w,h,d):
    """Sum z²/(2d)+z/2 over z=w−k(d−1), with all z nonnegative."""
    count = h+1
    sum_k = h*count//2
    sum_k2 = h*count*(2*h+1)//6
    step = d-1
    return F(count*(w*w+d*w)-sum_k*step*(2*w+d)+sum_k2*step**2,2*d)


def contact_intervals(v,lo,hi,t,d,b,stock):
    r = 3000
    max_order = hi//d+v
    retained = stock-b*b
    def cost(h,lam):
        def local(o):
            q = max(0,r-lam*o)
            return rank(q,h)-rank(q-o,h-v)
        return N*max(local(o) for o in range(max_order+1))

    candidates = [(h,lam,cost(h,lam)) for h,lam in BOARDS[v]]
    def on_piece(left,right,h,lam,price,gap):
        def cutoff(w):
            return (r-gap)*t-lam*(t+w-d+1)
        max_w,min_w = cutoff(left),cutoff(right)
        if min_w-right < h*(d-1):
            return None
        if retained*gap*t <= (r*t-min_w)*(v*((max_w-1)//d)+h*b):
            return None
        curvature = v*lam**2-(h-v+1)*(2*lam+1)
        require(curvature<=0, 'concave smooth quotient')
        def margin(w):
            wt = cutoff(w)
            return (smooth_slots(wt,h,d)-smooth_slots(wt-w,h-v,d)
                    -F((h-v+1)*d,8)-price)
        return min(margin(left),margin(right))

    cuts = [lo+(hi-lo)*i//256 for i in range(257)]
    worst = None
    for left,right in zip(cuts,cuts[1:]):
        accepted = False
        for h,lam,price in candidates:
            for gap in (1,2,3,4):
                gain = on_piece(left,right,h,lam,price,gap)
                if gain is not None and gain>0:
                    worst = gain if worst is None else min(worst,gain)
                    accepted = True
                    break
            if accepted:
                break
        require(accepted,f'contact board for v={v} at weights [{left},{right}]')
    return worst.__floor__()


def verify():
    d = N//16-1
    t = (F(473,2000)*N).__ceil__()
    p = 9*t
    b = (p-1)//(d-1)
    stock = N//13
    require(slots(p,4,d)>N*rank(9,4) and 4*stock+b<=N, 'primary and small groups')
    require(stock>b*((3000*t-1)//(d-1)), 'linear secondary Bezout')
    linear(d,t,p,b,8,False)
    require(max(7+12*d,F(N-d,t-d))+3*stock+b <= N, 'linear list budget')
    middle = middle_weights(d,t,stock,b,COEFFICIENT_ROWS)
    gains = []
    for v in (2,3,4):
        lo = 6*d-2 if v==2 else 4*(d-1)
        gains.append(contact_intervals(v,lo,p-1,t,d,b,stock))
        if v<4:
            require(curve_bound(3,v,d,t)+(4-v)*stock+b <= N, 'small residual budget')
    require(N-t==819_801_882, 'closed sixteenth-rate endpoints')
    print(f'Both sixteenth-rate fields are safe through {N-t:,} errors at list cap n. '
          f'Coefficient surplus {middle:,}. Factor-order surpluses {gains}.')


if __name__=='__main__':
    verify()
