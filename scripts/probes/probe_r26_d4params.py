import math
# d=4 face budgets (from _R25D4Instantiate.quintic_kernel_fiber_bound):
#  count: m(D+4m+J) < 4J(D+1)
#  indep: 4D+15 < q
#  m < q ; e=(q-1)/4
#  fiber: m*#N <= 5(m+3e)+D+q(J-1)  => B = that /m
# fold: 4B - q + 3 <= C sqrt q   (|T|=4, zero fiber <=3)
def excess(q,m,J,D):
    e=(q-1)//4
    if not(4*D+15<q): return None
    if not(m*(D+4*m+J) < 4*(J*(D+1))): return None
    if not(0<m<q and J>0): return None
    B=(5*(m+3*e)+D+q*(J-1))/m
    return 4*B - q + 3
best={}
for q in [101,1009,10007,100003,1000003,65537,2**20+7]:
    bb=None
    sm=int(math.isqrt(q))
    for m in range(1,6*sm):
        for dj in range(0,80):
            J=m//4+1+dj
            # D at cap
            D=(q-16)//4
            v=excess(q,m,J,D)
            if v is not None and (bb is None or v<bb[0]/1e18 or v<bb[0]):
                if bb is None or v<bb[0]: bb=(v,m,J,D)
    if bb: print(q, "best excess=%.1f"%bb[0], "C=%.4f"%(bb[0]/math.sqrt(q)), "m=%d J=%d D=%d"%bb[1:])
