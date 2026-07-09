import numpy as np, math, random

def is_prime(n):
    if n<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31]:
        if n%p==0: return n==p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a>=n: continue
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: ok=True;break
        if not ok: return False
    return True

def primroot(p):
    if p==2: return 1
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g

def v2(x):
    c=0
    while x%2==0: x//=2; c+=1
    return c

# Find primes where n=2^a is the FULL 2-part (=> m odd), small p
def find_prize_primes(a, want=3, cap=200000):
    n=2**a; out=[]
    # p-1 = n*m, m odd, p prime
    m=1
    while len(out)<want and n*m+1<cap:
        if m%2==1:
            p=n*m+1
            if is_prime(p) and v2(p-1)==a:
                out.append((p,n,m))
        m+=1
    return out

def analyze(p,n):
    g=primroot(p); m=(p-1)//n
    powg=np.empty(p-1,dtype=np.int64); cur=1
    for k in range(p-1): powg[k]=cur; cur=cur*g%p
    dlog=np.empty(p,dtype=np.int64); dlog[powg]=np.arange(p-1)
    sub=powg[np.arange(0,p-1,m)]
    ep=np.exp(2j*np.pi*np.arange(p)/p)
    klog=dlog[1:p]; js=np.arange(m)
    expo=(np.outer(js*n,klog))%(p-1)
    psi_jt=np.exp(2j*np.pi*expo/(p-1))
    taus=psi_jt @ ep[1:p]
    sqp=math.sqrt(p); a=taus/sqp
    coset_reps=powg[:m]
    eta_cr=np.array([ep[(int(b)*sub)%p].sum() for b in coset_reps])
    Fc=np.array([(taus*np.exp(-2j*np.pi*c*js/m)).sum() for c in range(m)])
    den=np.max(np.abs(m*eta_cr))+1e-12
    r1=float(np.max(np.abs(Fc-m*eta_cr))/den)
    bs=np.arange(1,p); bx=(bs[:,None]*sub[None,:])%p
    etaall=ep[bx].sum(axis=1)
    B=float(np.max(np.abs(etaall))); L2=float(math.sqrt(np.mean(np.abs(etaall)**2)))
    sumsq=float(np.sum(np.abs(etaall)**2)); sumsq_pred=((m-1)*p+1)/m
    Bsqn=B/math.sqrt(n*math.log(m)) if m>1 else 0.0
    # R3 cocycle
    viol=0; checks=0; maxd=0.0
    t=np.arange(1,p)
    for _ in range(30):
        i=random.randrange(1,m); j=random.randrange(1,m)
        if (i+j)%m==0: continue
        oneminus=(1-t)%p
        psii_t=psi_jt[i%m]
        valid=oneminus!=0
        psij=np.zeros(p-1,dtype=complex)
        idx=dlog[oneminus[valid]]
        psij[valid]=np.exp(2j*np.pi*(j*n*idx)/(p-1))
        J=np.sum(psii_t*psij)
        lhs=a[i]*a[j]; rhs=(J/sqp)*a[(i+j)%m]
        d=abs(lhs-rhs); maxd=max(maxd,d); checks+=1
        if d>1e-6: viol+=1
    # R4 chirp 2nd-order
    M=m; aa=a
    d2=np.array([aa[(j+2)%M]*aa[j%M]*np.conj(aa[(j+1)%M])**2 for j in range(1,M-2)])
    d2=d2/np.abs(d2); circvar=1-float(np.abs(np.mean(d2)))
    # R5 doubling bijective on Z/m (trivially true for odd m); also test HD duplication needs m even
    doubling_biject = (math.gcd(2,m)==1)
    return dict(p=p,n=n,m=m,m_odd=(m%2==1),v2pm1=v2(p-1),log2n=int(round(math.log2(n))),
                r1=r1, B=round(B,3),L2=round(L2,3),BoverL2=round(B/L2,3),Bsqn=round(Bsqn,3),
                sumsq=round(sumsq,1),sumsq_pred=round(sumsq_pred,1),
                cocyc_viol=viol,cocyc_checks=checks,cocyc_maxd=round(maxd,8),
                chirp_circvar=round(circvar,4), doubling_biject=doubling_biject)

random.seed(2)
print("# PRIZE-REGIME (n = full 2-part of p-1, so m ODD):", flush=True)
for a in [3,4,5]:
    for (p,n,m) in find_prize_primes(a, want=2, cap=120000):
        print(analyze(p,n), flush=True)
