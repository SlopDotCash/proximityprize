import numpy as np, math

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

def chk(p,n):
    g=primroot(p); m=(p-1)//n
    powg=np.empty(p-1,dtype=np.int64); cur=1
    for k in range(p-1): powg[k]=cur; cur=cur*g%p
    sub=powg[np.arange(0,p-1,m)]
    ep=np.exp(2j*np.pi*np.arange(p)/p)
    bs=np.arange(1,p); bx=(bs[:,None]*sub[None,:])%p
    etaall=ep[bx].sum(axis=1)
    sumsq_all = float(np.sum(np.abs(etaall)**2))                  # over all b != 0
    L2_all = math.sqrt(sumsq_all/(p-1))                          # rms over b!=0
    # distinct-period interpretation: m distinct values, sum over the m coset-reps:
    eta_cr=etaall[powg[:m]-1] if False else np.array([ep[(int(b)*sub)%p].sum() for b in powg[:m]])
    sumsq_cosets=float(np.sum(np.abs(eta_cr)**2))
    return dict(p=p,n=n,m=m,m_odd=(m%2==1),
        sumsq_over_all_bnz=round(sumsq_all,2),
        identity_n_times_pm1=n*(p-1),
        claimed_pred=round(((m-1)*p+1)/m,2),
        L2_rms_over_b=round(L2_all,4), sqrt_n=round(math.sqrt(n),4),
        sumsq_over_m_cosets=round(sumsq_cosets,2),
        per_coset_mean_sq=round(sumsq_cosets/m,3))

# n=full 2-part (m odd) AND n not full (m even) for contrast
cases=[(41,8),(73,8),(4129,8),(1048609,32)]
for (p,n) in cases:
    if is_prime(p) and (p-1)%n==0:
        print(chk(p,n), flush=True)
