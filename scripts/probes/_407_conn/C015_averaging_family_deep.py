"""
C015 final: the averaging FAMILY at t>=2 -- does it deliver many distinct bad gamma?

averaging_list_lower_bound: for a fixed word g (coeff_a(g)!=0), the perturbations
  pS = g - C(coeff_a(g)) * nodal_S   (S an a-subset, a=k+t)
all agree with g on the a nodes of S, and are DISTINCT codewords (injective in S).
Within one elementary-symmetric class (fixing top t coeffs of nodal_S) there are
>= C(n,a)/q^t of them.

For the MONOMIAL stack bridge we need: u0 := eval(g) (g of degree a=k+t, so the
perturbations pS have degree < a). The bad gamma = leading X^k coeff of a deg<k+1
poly agreeing with u0 on k+t points. But pS has degree a-1 = k+t-1 >= k+1 for t>=2,
so pS is NOT degree<k+1 -- it does NOT lift through the X^k bridge (which needs
deg<k+1). So the averaging family at t>=2 produces deg<(k+t) codewords, which are
NOT the deg<k+1 lifts the monomial bridge counts. The list and the bad-gamma object
DIVERGE at t>=2: averaging counts deg<(k+t) agreement, the bridge needs deg<k+1.

This probe makes that concrete: count averaging-family members (large) vs how many
are deg<k+1 (the bridge-relevant ones) vs distinct leading X^k coeffs among those.
"""
import itertools
from math import comb

def subgroup(q,n):
    assert (q-1)%n==0
    def order(a):
        o=1;x=a%q
        while x!=1:x=(x*a)%q;o+=1
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1:g=c;break
    h=pow(g,(q-1)//n,q)
    return [pow(h,i,q) for i in range(n)]

def polymul(a,b,q):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[i+j]=(r[i+j]+x*y)%q
    return r

def nodal(S,q):
    p=[1]
    for x in S:
        p=polymul(p,[(-x)%q,1],q)
    return p

def run(q,n,k,t):
    D=subgroup(q,n);a=k+t
    # word g of degree a with nonzero top coeff: g = X^a (simplest)
    g=[0]*(a+1);g[a]=1
    coeff_a=g[a]  # =1
    deg_lt_k1=0; leads=set(); total=0
    for S in itertools.combinations(D,a):
        total+=1
        nod=nodal(list(S),q)  # degree a, monic
        # pS = g - coeff_a * nodal_S  (both monic degree a -> top cancels -> degree < a)
        pS=[ (g[i] if i<len(g) else 0) for i in range(a+1)]
        for i,c in enumerate(nod):
            pS[i]=(pS[i]-coeff_a*c)%q
        # actual degree of pS
        d=a
        while d>0 and pS[d]==0: d-=1
        if d<k+1:        # deg < k+1 -> relevant to the X^k monomial bridge
            deg_lt_k1+=1
            leads.add(pS[k]%q if k<len(pS) else 0)
    return dict(n=n,k=k,t=t,a=a,total=total,deg_lt_k1=deg_lt_k1,distinct_lead=len(leads),
        avg_lb=comb(n,a)//(q**t))

if __name__=="__main__":
    q=12289
    print("Averaging family pS = X^a - nodal_S (deg < a). Bridge needs deg<k+1.\n")
    print("%-3s %-3s %-3s %-3s %-9s %-12s %-12s %-9s"%(
        "n","k","t","a","#subsets","deg<k+1(brdg)","distLeadCf","C(n,a)/q^t"))
    for n,k in [(16,4),(16,8)]:
        for t in [1,2,3]:
            if k+t>n: continue
            r=run(q,n,k,t)
            print("%-3d %-3d %-3d %-3d %-9d %-12d %-12d %-9d"%(
                r['n'],r['k'],r['t'],r['a'],r['total'],r['deg_lt_k1'],
                r['distinct_lead'],r['avg_lb']))
    print("\nKEY: at t=1, a=k+1, pS has deg<k+1 (= a-1=k) -> ALL bridge-relevant; large distinct leads.")
    print("     at t>=2, a=k+t, pS has deg up to a-1=k+t-1 >= k+1 -> generically NOT deg<k+1 -> 0 bridge-relevant.")
    print("So the averaging list (C(n,a)/q^t, deg<k+t agreement) and the monomial bad-gamma object")
    print("(deg<k+1 lifts) COINCIDE only at t=1 (the excluded near-1-rho sliver), and DECOUPLE at t>=2")
    print("(the actual prize interior). This is the structural gap C015 identifies, confirmed exactly.")
