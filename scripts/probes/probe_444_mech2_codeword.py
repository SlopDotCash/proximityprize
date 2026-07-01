"""
probe_444_mech2_codeword.py -- THE codeword candidate, done right, for r=3,4,5,6.

Reframing (proven): gamma bad <=> word W_gamma(x)=x^e+gamma x^f agrees with a deg<r poly P_gamma at
>= r+1 points of mu_n.  The DIFFERENCE D_gamma=W_gamma - P_gamma vanishes on the bad subset S
(>= r+1 pts).  P_gamma is the genuine 'r-1 data' (deg<r => r coeffs, but homogeneity/normalization
removes some).

We extract, per J (using a canonical bad S), the codeword P_gamma (its r coefficients), then form
DILATION-INVARIANT data from it and test injectivity J -> invariant and whether the invariant lives
on mu_{n/2}.

Dilation: x->gx sends W_gamma -> W_{gamma'} with gamma'=g^{e-f}gamma, and P_gamma(x)->P(gx) i.e.
coeff c_j -> c_j g^j.  So the RATIOS c_j / c_0 g^{-j}... the invariant under c_j->c_j g^j is e.g.
c_j^{n} / c_0^{?}.  Cleanest: the ROOTS of P_gamma scale by g, so {root_i} -> {g root_i}: the
MULTISET of root-RATIOS {root_i/root_0} is dilation invariant.  And P_gamma deg<=r-1 => <= r-1 roots
=> an (r-1)-subset (the root ratios)!  If those root-ratios land in mu_{n/2} (squares) -> EXACTLY the
(r-1)-subset-of-squares we want.

So candidate Phi(J) := { root_i / root_{lex-min} : roots of P_gamma } -- an (<=r-1)-subset of F_p,
hopefully in mu_{n/2}.  Test: well-defined per J, injective, image in (r-1)-subsets of mu_{n/2}.
NOTE roots may be OUTSIDE mu_n (P_gamma is a generic deg<r poly).  Measure where they live.
"""
import sys
from math import comb, gcd
from itertools import combinations
from collections import Counter, defaultdict

P=2013265921
def gen(n,p=P):
    e=(p-1)//n
    for c in range(2,2000):
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
def collect(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list); Mmax=max(e-r+1,f-r+1)
    if min(e-r,f-r)<0: return w,{},d,nd
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J2S[pow(g,nd,p)].append((Sidx,g))
    return w,J2S,d,nd

def interp_coeffs(pts,vals,p=P):
    """deg < len(pts) interpolant coeffs low->high."""
    rr=len(pts); coeffs=[0]*rr
    for t in range(rr):
        num=[1]; den=1
        for s in range(rr):
            if s!=t:
                new=[0]*(len(num)+1)
                for i,c in enumerate(num):
                    new[i]=(new[i]-c*pts[s])%p; new[i+1]=(new[i+1]+c)%p
                num=new; den=den*((pts[t]-pts[s])%p)%p
        inv=pow(den,p-2,p)*vals[t]%p
        for i,c in enumerate(num): coeffs[i]=(coeffs[i]+c*inv)%p
    return coeffs

def poly_roots_in(coeffs,domain,p=P):
    out=[]
    for x in domain:
        v=0; xp=1
        for c in coeffs:
            v=(v+c*xp)%p; xp=xp*x%p
        if v==0: out.append(x)
    return out

def study(n,r,e,f):
    w,J2S,d,nd=collect(n,r,e,f)
    OP=len(J2S)
    print(f"\n  r={r} n={n} (x^{e},x^{f}) parity({e%2},{f%2}): O_P={OP} C(n/2,r-1)={comb(n//2,r-1)}")
    if OP==0: print("   none"); return
    allF=None
    is_sq=lambda a: a!=0 and pow(a,(P-1)//2,P)==1
    J2inv=defaultdict(set)
    rootloc=Counter()  # where do P_gamma roots live: in mu_n? squares? generic?
    rootcount=Counter()
    muN={pow(w,i,P):i for i in range(n)}
    for J,Ss in J2S.items():
        for Sidx,g in Ss:
            xs=[pow(w,i,P) for i in Sidx]
            vals=[(pow(x,e,P)+g*pow(x,f,P))%P for x in xs]
            # interpolate deg<r through first r of the r+1 pts (the (r+1)th is the consistency)
            coeffs=interp_coeffs(xs[:r],vals[:r])
            # roots in mu_n
            rt=poly_roots_in(coeffs,[pow(w,i,P) for i in range(n)])
            rootcount[len(rt)]+=1
            for x in rt:
                rootloc['inMuN']+=1
                rootloc['square' if is_sq(x) else 'nonsq']+=1
            # dilation-invariant: root-ratios to a canonical root (lex-min index). Need >=1 root.
            if rt:
                ridx=sorted(muN[x] for x in rt)
                base=ridx[0]
                inv=frozenset((ri-base)%n for ri in ridx)
                J2inv[J].add(inv)
            else:
                J2inv[J].add(('NOROOT',))
    const=all(len(v)==1 for v in J2inv.values())
    nd_=len(set(next(iter(v)) for v in J2inv.values())) if const else -1
    print(f"    P_gamma root-count dist (in mu_n)={dict(rootcount)}; root locations={dict(rootloc)}")
    print(f"    Phi=root-ratio-set: const-per-J={const} #distinct={nd_} inj={nd_==OP} "
          f"<=C(n/2,r-1)? {nd_<=comb(n//2,r-1) if nd_>0 else '?'}")

if __name__=="__main__":
    LINES={3:(lambda n:(n//2,n//2-1)),4:(lambda n:(n//2+2,n//4+1)),
           5:(lambda n:(n//2+1,n-1)),6:(lambda n:(n//2+4,n//2+2))}
    todo=[(3,16),(4,16),(5,16),(6,16),(3,32),(4,32)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
