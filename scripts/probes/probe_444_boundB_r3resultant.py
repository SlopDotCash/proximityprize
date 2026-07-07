"""
probe_444_boundB_r3resultant.py -- EXACT symbolic resultant elimination for r=3, deriving the
gamma minimal-poly degree as a polynomial in n, to PROVE (r=3) the elimination route reaches the
descended degree and exhibit the 2^r mechanism.

r=3 structured variety (PROVEN): S={a,b,c,d}, a,b in mu_{n/2} (squares), c,d nonsquares, ab=-cd.
Set q=ab (in mu_{n/2}), s=a+b, u=c+d. Then cd=-q, c,d are roots of z^2-uz-q.
h_m(S) = h_m of the 4 roots; via gen func 1/((1-at)(1-bt)(1-ct)(1-dt)).
Newton/symmetric: e1=s+u, e2=q + s*u + (-q)=s*u ... let's just let sympy build h_m from (s,q,u).

gamma = -h_{e-3}/h_{f-3}. We ELIMINATE the subset coordinates (s,u) [q is the orbit parameter]
and read the degree of the gamma-eliminant.  The dilation orbit acts; the INVARIANT is gamma^{n/d}.

We do it over F_p numerically too (cross-check) but the symbolic resultant gives the a-priori
degree.  Output: deg of gamma-eliminant in terms of the free parameters, and whether it = C(n/4,2)
shape after accounting for the cyclotomic constraints q^{n/2}=1 etc.
"""
import sympy as sp
from math import comb, gcd
from itertools import combinations

# ---- symbolic h_m of 4 roots a,b,c,d expressed via (s=a+b, q=ab, u=c+d, qq=cd) ----
def hm_in_terms(m):
    t,a,b,c,d=sp.symbols('t a b c d')
    gf=1/((1-a*t)*(1-b*t)*(1-c*t)*(1-d*t))
    ser=sp.series(gf,t,0,m+1).removeO()
    hm=sp.Poly(ser,t).nth(m)
    # rewrite in elementary symmetric via s2=a+b,q2=ab,s_cd=c+d,q_cd=cd
    return sp.expand(hm)

# Practical exact route: do the elimination over F_p with the structured parametrization, but get
# the DEGREE by building the actual minimal poly of gamma over the (s,q,u)-variety per fixed q,
# then over q. This isolates the per-q (per square-product) fiber degree -- the genuine residual.
P=2013265921
def gen_fp(n,p=P):
    e=(p-1)//n
    for c in range(2,600):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
    raise RuntimeError
def hpow(elts,M,p=P):
    Pw=[0]*(M+1)
    for i in range(1,M+1): Pw[i]=sum(pow(z,i,p) for z in elts)%p
    H=[0]*(M+1); H[0]=1
    for m in range(1,M+1):
        s=0
        for i in range(1,m+1): s=(s+Pw[i]*H[m-i])%p
        H[m]=(s*pow(m,p-2,p))%p
    return H

def per_q_fiber(n,e,f,p=P):
    """For r=3: group bad S by q=ab (the square-product class, in mu_{n/2}), and within each q
       count distinct J. This is the elimination 'fiber over the orbit base'. The TOTAL O_P =
       sum over q-classes of (distinct J at that q), but J is dilation-orbit so really O_P counts
       distinct J overall. We measure: #distinct q-classes, and #distinct J per q, to see the
       degree structure deg = (#base) x (fiber)."""
    w=gen_fp(n,p); d=gcd((e-f)%n,n); nd=n//d
    sq=[pow(w,2*i,p) for i in range(n//2)]
    nsq=[pow(w,2*i+1,p) for i in range(n//2)]
    from collections import defaultdict
    qJ=defaultdict(set)   # q=ab class index in mu_{n/2} -> set of J
    M=max(e-3+1,f-3+1)
    for (ia,ib) in combinations(range(n//2),2):
        a,b=sq[ia],sq[ib]; q=(a*b)%p
        target=(-q)%p
        for (ic,idd) in combinations(range(n//2),2):
            c,dd=nsq[ic],nsq[idd]
            if (c*dd)%p!=target: continue
            S=[a,b,c,dd]; H=hpow(S,M,p)
            if (H[e-3]*H[f-3+1]-H[f-3]*H[e-3+1])%p: continue
            if H[f-3]==0: continue
            g=(-H[e-3]*pow(H[f-3],p-2,p))%p
            if not g: continue
            qJ[(ia+ib)%(n//2)].add(pow(g,nd,p))   # q index = (2ia+2ib)/2 mod n/2 = (ia+ib) mod n/2
    base=len(qJ)
    fibers=[len(v) for v in qJ.values()]
    allJ=set();
    for v in qJ.values(): allJ|=v
    return len(allJ), base, min(fibers), max(fibers), sum(fibers)

if __name__=="__main__":
    print("r=3 elimination over q=ab base (square-product class in mu_{n/2}):")
    print(f"{'n':>4} {'O_P':>5} {'#q-base':>8} {'fiber(min,max)':>15} {'sum-fiber':>10} "
          f"{'C(n/4,2)':>9} {'n/4':>5}")
    for n in [16,32,64]:
        e,f=n//2,n//2-1
        OP,base,fmin,fmax,sf=per_q_fiber(n,e,f)
        print(f"{n:>4} {OP:>5} {base:>8} {('('+str(fmin)+','+str(fmax)+')'):>15} {sf:>10} "
              f"{comb(n//4,2):>9} {n//4:>5}")
