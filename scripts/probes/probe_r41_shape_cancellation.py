import numpy as np, math
from sympy import isprime
def factor(x):
    fs,d=set(),2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in factor(p-1)): return g
def run(p,n):
    g=prim_root(p); m=(p-1)//n
    ind={}; x=1
    for k in range(p-1): ind[x]=k; x=x*g%p
    ks=np.array([ind[a] for a in range(1,p)])
    chi_full=np.zeros(p); chi_full[1:]=np.where(ks%2==0,1.0,-1.0)
    ts=np.arange(p); om=(1-ts)%p
    J=np.zeros(m,dtype=complex)
    for jj in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*jj*n*ks/(p-1))
        J[jj]=np.sum(lv[ts]*chi_full[om])
    Jm=J.copy(); Jm[0]=0
    tc=np.fft.ifft(np.fft.fft(Jm)**3)
    E3=float(np.sum(np.abs(tc)**2))
    jv=np.arange(m)
    rng=np.random.default_rng(3)
    nsamp=300
    vals=[]
    for _ in range(nsamp):
        a,b,ap=rng.integers(0,m,3)
        t=int(rng.integers(0,m)); bp=(3*t+a+b-ap)%m
        corr=np.sum(Jm[(jv+t)%m]*Jm[(jv+t+a)%m]*Jm[(jv+t+b)%m]
                    *np.conj(Jm[jv]*Jm[(jv+ap)%m]*Jm[(jv+bp)%m]))
        vals.append(abs(corr))
    mean_abs=float(np.mean(vals))
    nshapes=m**4  # (a,b,a',b') free... with t determined iff gcd(3,m)=1; else t multi — use m^4 as count proxy
    est_naive=mean_abs*nshapes
    print(f"p={p:>6} n={n:>3} m={m:>4}: E3={E3:.3e}  naive-shape-sum≈{est_naive:.3e}  "
          f"cancellation factor={est_naive/E3:.1f}x  (loss predicted m^1.5·√n={m**1.5*math.sqrt(n):.0f})")
for (p,n) in [(577,8),(1153,32),(4129,16)]:
    run(p,n)
