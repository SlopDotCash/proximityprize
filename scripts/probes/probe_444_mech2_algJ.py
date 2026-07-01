"""
probe_444_mech2_algJ.py -- determine the ALGEBRAIC nature of J and whether sqrt(J) (J is always a
square) lives in mu_n, giving a natural (r-1)-subset.

Tests:
 (A) J is a square. Take a square root s=sqrt(J) (the one in the canonical coset). Is s in mu_n?
     mu_{n/2}? Compute order of s. If s in mu_n -> s=w^k, and k might be a SUM over an (r-1)-subset.
 (B) gamma itself: gamma(gS)=g^{e-f}gamma(S). Is gamma a RATIO of two products over subsets of S?
     gamma=-h_{e-r}(S)/h_{f-r}(S).  h_{m}(S) for the (r+1)-set S.  For r=3, e-r=n/2-3, f-r=n/2-4.
     These are HIGH-degree complete-homog of a 4-element set.  By the dual (h of a finite set relates
     to 1/prod(1-x_i t)), h_m(S)=sum over multi-indices.  Express gamma in CLOSED form.
 (C) The clean r=3 fact ab=-cd: so the 4 roots satisfy a relation. gamma should be a symmetric fn.
     Compute gamma for r=3 explicitly and match to a*b (=-c*d) and the ratios.

We compute gamma & J for canonical S and FIT against monomials in e_k(S), p_k(S), and the squared
elementary symmetric e_k(S^2) where S^2={x_i^2} in mu_{n/2}.  The (r-1)-subset of mu_{n/2} target
suggests J ~ e_{r-1}(squared roots)/e_0 or a ratio of consecutive e_k(S^2).
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
def esym(elts,p=P):
    """all elementary symmetric e_0..e_k of elts."""
    E=[1]
    for x in elts:
        new=E[:]+[0]
        for i in range(len(E)):
            new[i+1]=(new[i+1]+E[i]*x)%p
        E=new
    return E
def collect(n,r,e,f,p=P):
    w=gen(n,p); a0=r+1; d=gcd((e-f)%n,n); nd=n//d
    J2S=defaultdict(list); Mmax=max(e-r+1,f-r+1)
    for Sidx in combinations(range(n),a0):
        xs=[pow(w,i,p) for i in Sidx]
        H=hpow(xs,Mmax,p)
        if (H[e-r]*H[f-r+1]-H[f-r]*H[e-r+1])%p: continue
        if H[f-r]==0: continue
        g=(-H[e-r]*pow(H[f-r],p-2,p))%p
        if not g: continue
        J2S[pow(g,nd,p)].append((Sidx,g))
    return w,J2S,d,nd

def msqrt(a,p=P):
    """sqrt mod p (p=1 mod 4 here, Tonelli simplified via p%4). Use general Tonelli-Shanks."""
    if a==0: return 0
    if pow(a,(p-1)//2,p)!=1: return None
    # Tonelli-Shanks
    q=p-1; s=0
    while q%2==0: q//=2; s+=1
    if s==1: return pow(a,(p+1)//4,p)
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m=s; c=pow(z,q,p); t=pow(a,q,p); rr=pow(a,(q+1)//2,p)
    while t!=1:
        i=0; tt=t
        while tt!=1: tt=tt*tt%p; i+=1
        b=pow(c,1<<(m-i-1),p); m=i; c=b*b%p; t=t*c%p; rr=rr*b%p
    return rr

def study(n,r,e,f):
    w,J2S,d,nd=collect(n,r,e,f)
    OP=len(J2S)
    dl={pow(w,i,P):i for i in range(n)}
    print(f"\n  r={r} n={n} (x^{e},x^{f}): O_P={OP} C(n/2,r-1)={comb(n//2,r-1)} nd={nd}")
    if OP==0: return
    # (A) sqrt(J) in mu_n? order?
    inmu=0; muhalf=0; sqrt_idx=[]
    for J in J2S:
        s=msqrt(J)
        loc='gen'
        if pow(s,n,P)==1: inmu+=1; loc='muN'
        if pow(s,n//2,P)==1: muhalf+=1
        # also try gamma^{nd/2} if nd even
    print(f"    (A) sqrt(J) in mu_n: {inmu}/{OP}; in mu_(n/2): {muhalf}/{OP}")
    # (C) fit gamma against e_k(S^2): compute squared-root elementary symmetric & ratios
    # candidate: J ?= ratio involving e_{r-1}(S^2) over e_{r-2}(S^2) raised to nd, etc.
    # Test: is J determined by the unordered (r-1)-subset = the e_k(S^2) profile up to dilation?
    # Build invariant: e_k(S^2) scales as g^{2k} under dilation; so e_k(S^2)/e_1(S^2)^k is invariant.
    J2prof=defaultdict(set)
    for J,Ss in J2S.items():
        for Sidx,g in Ss:
            sq=[pow(w,(2*i)%n,P) for i in Sidx]   # squared roots in mu_{n/2}
            E=esym(sq)  # e_0..e_{r+1}
            # dilation-invariant normalized profile: e_k * e_1^{-k} for k=2..r+1 (e_1 scales g^2,e_k g^{2k})
            if E[1]==0: J2prof[J].add(('e1zero',)); continue
            inv1=pow(E[1],P-2,P)
            prof=tuple((E[k]*pow(inv1,k,P))%P for k in range(2,r+2))
            J2prof[J].add(prof)
    const=all(len(v)==1 for v in J2prof.values())
    nd_=len(set(next(iter(v)) for v in J2prof.values())) if const else -1
    print(f"    (C) squared-root e_k profile (dilation-normalized): const-per-J={const} "
          f"#distinct={nd_} inj={nd_==OP}")

if __name__=="__main__":
    LINES={3:(lambda n:(n//2,n//2-1)),4:(lambda n:(n//2+2,n//4+1)),
           5:(lambda n:(n//2+1,n-1)),6:(lambda n:(n//2+4,n//2+2))}
    todo=[(3,16),(4,16),(5,16),(6,16)]
    if len(sys.argv)>1: todo=[tuple(map(int,a.split(':'))) for a in sys.argv[1:]]
    for (r,n) in todo:
        e,f=LINES[r](n); study(n,r,e,f)
