"""
C015 deep test: does the non-degenerate (u0, X^k) stack still fire bad scalars at
DEEPER radius (t >= 2, i.e. a = k+t agreement points), the actual prize window
(1-sqrt(rho), 1-rho-Theta(1/log n)), not just the t=1 sliver next to 1-rho?

At t>=2: agreement on a=k+t points OVER-determines a deg<=k poly (a > k+1).
So a deg<k+1 interpolant through a points exists ONLY if those a points already
lie on a common deg<k+1 poly. The averaging construction guarantees this by
construction (pS agrees with g on the a nodes), but for a GENERIC received word u0
most a-subsets have NO deg<k+1 explanation -> the bad-gamma list collapses.

We measure, for the non-degenerate monomial stack with u0 = eval of a deg-(k+1)
word g0 (so SOME deg<k+1 explanation always exists -- the averaging family):
  - at t>=2, how many DISTINCT bad gamma survive (distinct leading X^k coeffs of
    deg<k+1 polys agreeing with u0 on >= k+t points, with non-matchable second row)
This is the radius the prize actually lives at.
"""
import itertools
from math import comb, sqrt, log

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

def lagrange(points,q):
    n=len(points);coeffs=[0]*n
    for j in range(n):
        xj,yj=points[j];num=[1];den=1
        for m in range(n):
            if m==j:continue
            xm=points[m][0];nn=[0]*(len(num)+1)
            for i,c in enumerate(num):
                nn[i]=(nn[i]+c*(-xm))%q;nn[i+1]=(nn[i+1]+c)%q
            num=nn;den=(den*(xj-xm))%q
        inv=pow(den%q,q-2,q);sc=(yj*inv)%q
        for i,c in enumerate(num):coeffs[i]=(coeffs[i]+c*sc)%q
    return coeffs

def peval(coeffs,x,q):
    r=0
    for c in reversed(coeffs):r=(r*x+c)%q
    return r

def fits_deg_lt(points,q,d):
    """Is there a deg<d poly through all points? Interp the first d, check rest."""
    if len(points)<=d:
        return lagrange(points,q)+[0]*(d-len(points))  # exists, return padded coeffs (deg<d)
    base=points[:d]
    c=lagrange(base,q)
    for (x,y) in points[d:]:
        if peval(c,x,q)!=y%q:
            return None
    return c

def run(q,n,k,t):
    D=subgroup(q,n);a=k+t
    # u0 = eval of a degree-(k+1) word g0 (the averaging family base): X^{k+1}-c0 X^k
    c0=D[1]
    g0=[0]*(k+2);g0[k+1]=1;g0[k]=(-c0)%q
    u0={x:peval(g0,x,q) for x in D}
    xk={x:pow(x,k,q) for x in D}
    bad=set();explain=0;mca=0;nsub=0
    for S in itertools.combinations(D,a):
        nsub+=1
        pts=[(x,u0[x]) for x in S]
        c=fits_deg_lt(pts,q,k+1)   # deg<k+1 explanation of u0 on S?
        if c is None: continue
        explain+=1
        lead=c[k] if len(c)>k else 0
        gamma=(-lead)%q
        # second row X^k: is there a deg<k poly agreeing with X^k on S?  (joint match needs both deg<k)
        pts1=[(x,xk[x]) for x in S]
        c1=fits_deg_lt(pts1,q,k)
        row0_low=(len(c)<=k) or all(c[j]==0 for j in range(k,len(c)))
        joint=(c1 is not None) and row0_low
        if not joint:
            mca+=1;bad.add(gamma)
    rho=k/n;delta=1-a/n
    win_lo=1-sqrt(rho);win_hi=1-rho
    return dict(n=n,k=k,t=t,a=a,nsub=nsub,explain=explain,distinct_bad=len(bad),mca=mca,
        delta=round(delta,3),win=f"({win_lo:.2f},{win_hi:.2f})",
        in_window=win_lo<delta<win_hi)

if __name__=="__main__":
    q=12289
    print("q=%d   (prize: q~n*2^128, q*eps*=n; need distinct_bad > n for a delta* upper bracket)\n"%q)
    print("%-3s %-3s %-3s %-3s %-7s %-9s %-9s %-7s %-7s %-12s %-7s"%(
        "n","k","t","a","nsub","explain","distBad","mca","delta","window","inWin"))
    for n,k in [(16,4),(16,8)]:
        for t in [1,2,3,4]:
            if k+t>n: continue
            r=run(q,n,k,t)
            print("%-3d %-3d %-3d %-3d %-7d %-9d %-9d %-7d %-7s %-12s %-7s"%(
                r['n'],r['k'],r['t'],r['a'],r['nsub'],r['explain'],r['distinct_bad'],
                r['mca'],r['delta'],r['win'],r['in_window']))
    print("\nInterpretation: 'explain' = # a-subsets with a deg<k+1 explanation of u0.")
    print("At t=1 (a=k+1) EVERY subset explains (interp always exists) -> explosion (sliver next to 1-rho).")
    print("At t>=2 (a>k+1) only subsets ON the averaging family explain -> count collapses toward C(deg, ...).")
    print("distBad = distinct bad gamma at this DEEPER radius = the operative prize quantity.")
