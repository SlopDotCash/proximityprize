# Part 2: GLT Fermat-hypersurface count + char-0 Bessel moment
import itertools, cmath, math
from collections import Counter

def primitive_root(p):
    phi=p-1; fac=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: fac.add(d); m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g

def setup(p,n):
    g=primitive_root(p); sub=sorted({pow(g,((p-1)//n)*k,p) for k in range(n)})
    etas=[sum(cmath.exp(2j*math.pi*(b*y%p)/p) for y in sub) for b in range(p)]
    return sub,etas

def Er(sub,p,r):
    c=Counter()
    for t in itertools.product(sub,repeat=r): c[sum(t)%p]+=1
    return sum(v*v for v in c.values())

def fermat_count(p,m,nv):
    single=Counter(pow(x,m,p) for x in range(p))
    dist={0:1}
    for _ in range(nv):
        nd={}
        for s,cn in dist.items():
            for v,c2 in single.items():
                nd[(s+v)%p]=nd.get((s+v)%p,0)+cn*c2
        dist=nd
    return dist.get(0,0)

# GLT claim (C010): Sum_s eta_s^{2r} = p^{2r-1} + ((p-1)/(p*m))*N  where
#   N = #{x_1^m+...+x_{2r}^m = 0}, m=(p-1)/n.  Note Sum_s eta_s^{2r} = p*E_r.
print("=== GLT: p*E_r =?= p^{2r-1} + ((p-1)/(pm))*FermatCount(2r vars) ===")
print(f"{'p':>5}{'n':>4}{'r':>3} | {'p*E_r':>10} {'GLT_rhs':>14} {'match':>6}")
for p,n in [(17,4),(17,8),(73,8),(97,4),(257,8)]:
    m=(p-1)//n
    sub,etas=setup(p,n)
    for r in [2,3]:
        lhs=p*Er(sub,p,r)
        nv=2*r
        N=fermat_count(p,m,nv)
        rhs=p**(2*r-1)+ (p-1)*N//(p*m)
        # careful integer: ((p-1)/(p*m)) * N -- check divisibility
        num=(p-1)*N
        den=p*m
        rhs_exact = p**(2*r-1) + num/den
        ok=abs(lhs-rhs_exact)<1e-6
        print(f"{p:>5}{n:>4}{r:>3} | {lhs:>10d} {rhs_exact:>14.2f} {str(ok):>6}")

# char-0 Bessel even-moment law (F13): E_r = (2r)! [x^r] I0(2 sqrt(x))^{n/2}
# I0(2 sqrt x) = sum_k x^k/(k!)^2 ; raise to n/2; coeff of x^r times (2r)!
def char0_Er(n,r):
    # I0(2 sqrt x)^(n/2) coefficient of x^r, times (2r)!
    # n must be even
    h=n//2
    # series of I0 up to degree r: a_k = 1/(k!)^2
    a=[1/(math.factorial(k)**2) for k in range(r+1)]
    # raise to power h via polynomial mult mod x^{r+1}
    poly=[1.0]+[0.0]*r
    for _ in range(h):
        np_=[0.0]*(r+1)
        for i in range(r+1):
            if poly[i]==0: continue
            for j in range(r+1-i):
                np_[i+j]+=poly[i]*a[j]
        poly=np_
    return poly[r]*math.factorial(2*r)

print("\n=== char-0 Bessel law: E_r^{char0} = (2r)![x^r] I0(2 sqrt x)^{n/2} ===")
print(f"{'n':>4}{'r':>3} | {'Bessel E_r':>14}  (compare to char-p E_r above when no anomaly)")
for n in [4,8,16]:
    for r in [2,3]:
        print(f"{n:>4}{r:>3} | {char0_Er(n,r):>14.1f}")
