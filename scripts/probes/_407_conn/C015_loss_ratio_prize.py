"""
C015 follow-up: the EXACT loss ratios and the prize-scale comparison.

From C015_nondegen_stack_loss.py we found, on the non-degenerate monomial stack
(u0, X^k) over mu_n in F_12289:
  - every a-subset is non-matchable  => mcaEvent fires (UNLIKE the degenerate (w,0))
  - but distinct-leading-coeff (= distinct bad gamma) << #subsets (the new loss)

This probe pins:
 (1) the loss ratio  distinct_bad_gamma / total_subsets  and its trend in n
 (2) whether distinct_bad_gamma can approach the q-scale (it is bounded by q-1)
 (3) the PRIZE comparison: bad-count vs C(n,a)/q^t (the averaging reverse bound)
     and vs the actual list size, and vs q*eps* = q*2^-128.

The structural point C015 makes: averaging_list_lower_bound gives list >= C(n,a)/q^t,
but at the prize q ~ n^beta >> C(n,a) so C(n,a)/q^t < 1 -> the REVERSE bound is
VACUOUS in regime. AND even the raw distinct-bad-gamma, while nonzero, is O(n^k)/...
We measure exactly.
"""
import itertools
from math import comb, log

def subgroup(q,n):
    assert (q-1)%n==0
    def order(a):
        o=1;x=a%q
        while x!=1: x=(x*a)%q;o+=1
        return o
    g=None
    for c in range(2,q):
        if order(c)==q-1: g=c;break
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

def run(q,n,k,t=1):
    D=subgroup(q,n);a=k+t
    c0=D[1]
    g0=[0]*(k+2);g0[k+1]=1;g0[k]=(-c0)%q
    u0={x:peval(g0,x,q) for x in D}
    xk={x:pow(x,k,q) for x in D}
    bad=set();all_lead=set();nsub=0;mca=0
    for S in itertools.combinations(D,a):
        nsub+=1
        ci=lagrange([(x,u0[x]) for x in S],q)
        lead=ci[k] if len(ci)>k else 0
        gamma=(-lead)%q;all_lead.add(gamma)
        ci1=lagrange([(x,xk[x]) for x in S],q)
        row1_low=all(ci1[j]==0 for j in range(k,len(ci1)))
        row0_low=all(ci[j]==0 for j in range(k,len(ci)))
        joint=row0_low and row1_low
        if not joint:
            mca+=1;bad.add(gamma)
    return dict(n=n,k=k,a=a,nsub=nsub,distinct_lead=len(all_lead),
        distinct_bad=len(bad),mca=mca,
        list_lb=comb(n,a),                  # actual averaging list size (= nsub here, all distinct)
        avg_reverse_lb=comb(n,a)//(q**t),   # the averaging_list_lower_bound value C(n,a)/q^t
        loss_ratio=round(len(bad)/nsub,4))

if __name__=="__main__":
    q=12289
    rows=[]
    for n,k in [(8,2),(8,4),(8,6),(16,4),(16,8),(16,12)]:
        rows.append(run(q,n,k))
    print("q=%d  prize threshold q*2^-128 = %.3e\n"%(q,q*2**-128))
    print("%-3s %-3s %-3s %-7s %-9s %-9s %-7s %-12s %-10s"%(
        "n","k","a","nsub","distBad","distLead","mca","avgRevLB","loss"))
    for r in rows:
        print("%-3d %-3d %-3d %-7d %-9d %-9d %-7d %-12d %-10s"%(
            r['n'],r['k'],r['a'],r['nsub'],r['distinct_bad'],r['distinct_lead'],
            r['mca'],r['avg_reverse_lb'],r['loss_ratio']))
    print("\nKEY: avgRevLB = C(n,a)/q^t (the averaging_list_lower_bound). At prize q>>C(n,a) this is 0/vacuous.")
    print("distBad = distinct bad gamma actually fired by the non-degenerate (u0,X^k) stack.")
    print("Need distBad > q*eps* = q*2^-128 ~ 3.6e-35 for a delta* UPPER bracket. distBad is O(n^k) but")
    print("the question is whether it ever exceeds q*eps*; numerically distBad>0 always, but that is the")
    print("trivial regime (eps*=2^-128 makes q*eps*<1, so ANY single bad gamma already 'crosses').")
    print("The real prize regime: q ~ n*2^128, eps*=2^-128 => q*eps* = n. So need distBad > n.")
    for r in rows:
        print("  n=%d k=%d: distBad=%d  vs  prize-threshold n=%d  => %s"%(
            r['n'],r['k'],r['distinct_bad'],r['n'],
            "EXCEEDS n" if r['distinct_bad']>r['n'] else "below n"))
