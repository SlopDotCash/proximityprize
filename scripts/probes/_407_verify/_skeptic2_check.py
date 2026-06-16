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

def analyze(p,n):
    g=primroot(p); m=(p-1)//n
    powg=np.empty(p-1,dtype=np.int64); cur=1
    for k in range(p-1): powg[k]=cur; cur=cur*g%p
    dlog=np.empty(p,dtype=np.int64); dlog[powg]=np.arange(p-1)
    sub=powg[np.arange(0,p-1,m)]                       # mu_n
    ep=np.exp(2j*np.pi*np.arange(p)/p)
    klog=dlog[1:p]                                     # dlog of t=1..p-1
    js=np.arange(m)
    expo=(np.outer(js*n,klog))%(p-1)
    psi_jt=np.exp(2j*np.pi*expo/(p-1))                 # psi^j(t), shape (m,p-1)
    taus=psi_jt @ ep[1:p]                              # tau(psi^j)
    sqp=math.sqrt(p); a=taus/sqp
    # parity of m
    m_odd = (m%2==1)
    # R1: m-DFT of tau over coset index c equals m*eta on coset reps g^c
    coset_reps=powg[:m]
    eta_cr=np.array([ep[(int(b)*sub)%p].sum() for b in coset_reps])
    Fc=np.array([ (taus*np.exp(-2j*np.pi*c*js/m)).sum() for c in range(m)])
    den=np.max(np.abs(m*eta_cr))+1e-12
    r1=np.max(np.abs(Fc-m*eta_cr))/den
    Fc2=np.array([ (taus*np.exp(2j*np.pi*c*js/m)).sum() for c in range(m)])
    r1b=np.max(np.abs(Fc2-m*eta_cr))/den
    # R2: full Parseval over all b!=0
    bs=np.arange(1,p)
    bx=(bs[:,None]*sub[None,:])%p
    etaall=ep[bx].sum(axis=1)
    B=float(np.max(np.abs(etaall)))
    L2=float(math.sqrt(np.mean(np.abs(etaall)**2)))
    sumsq=float(np.sum(np.abs(etaall)**2))
    sumsq_pred=((m-1)*p+1)/m
    Bsqn=B/math.sqrt(n*math.log(m)) if m>1 else 0.0
    BoverL2=B/L2
    # R3 Jacobi cocycle  a_i a_j = (J/sqrt(p)) a_{i+j}
    viol=0; checks=0; maxd=0.0
    for _ in range(40):
        i=random.randrange(1,m); j=random.randrange(1,m)
        if (i+j)%m==0: continue
        # J(psi^i,psi^j)=sum_t psi^i(t) psi^j(1-t).  use tables: t=1..p-1, 1-t mod p
        t=np.arange(1,p)
        oneminus=(1-t)%p
        psii_t = psi_jt[i%m]
        valid = oneminus!=0
        psij = np.zeros(p-1,dtype=complex)
        idx = dlog[oneminus[valid]]
        psij[valid]=np.exp(2j*np.pi*(j*n*idx)/(p-1))
        J=np.sum(psii_t*psij)
        lhs=a[i]*a[j]; rhs=(J/sqp)*a[(i+j)%m]
        d=abs(lhs-rhs); maxd=max(maxd,d); checks+=1
        if d>1e-6: viol+=1
    # R4 chirp test: is a_j a pure quadratic chirp a_j ~ exp(i(alpha j^2+...))?
    # 2nd difference of phase: phi_j - 2phi_{j+1}+phi_{j+2}; for pure quad chirp = const => circ var 0
    ang=np.angle(a[1:])  # drop j=0 (a_0 = tau_0/sqrt p = -1/sqrt p not unimodular)
    # 2nd diff of unwrapped won't be robust; use circular variance of e^{i*2nd diff} of a directly:
    # second-order phase increment delta2_j = a_{j+2} a_j conj(a_{j+1})^2 (unimodular ratio)
    aa=a
    M=m
    d2=np.array([ aa[(j+2)%M]*aa[j%M]*np.conj(aa[(j+1)%M])**2 for j in range(1,M-2)])
    d2=d2/np.abs(d2)
    R=np.abs(np.mean(d2)); circvar=1-R   # 0 => perfect chirp
    return dict(p=p,n=n,m=m,m_odd=m_odd,r1=r1,r1b=r1b,B=round(B,4),L2=round(L2,4),
                BoverL2=round(BoverL2,4),Bsqn=round(Bsqn,4),
                sumsq=round(sumsq,2),sumsq_pred=round(sumsq_pred,2),
                cocyc_viol=viol,cocyc_checks=checks,cocyc_maxd=round(maxd,2e0 and 8),
                chirp_circvar=round(circvar,4))

random.seed(1)
for (p,n) in [(4129,8),(32801,8),(65617,16),(1048609,32),(1048609,16)]:
    if is_prime(p):
        print(analyze(p,n), flush=True)
