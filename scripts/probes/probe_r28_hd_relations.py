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

def run(p,n,trials=20):
    g=prim_root(p); m=(p-1)//n
    if m%2: return
    ind={}; x=1
    for k in range(p-1): ind[x]=k; x=x*g%p
    ks=np.array([ind[a] for a in range(1,p)])
    # gauss sums of the family lam_j
    psi=np.exp(2j*np.pi*np.arange(p)/p)
    glam=np.zeros(m,dtype=complex)
    for j in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*j*n*ks/(p-1))
        glam[j]=np.sum(lv*psi)
    # verify HD d=2: g(l_j) g(l_{j+m/2}) = lam_j(4)^{-1} g(l_{2j mod m}) g(l_{m/2})
    errs=[]
    for j in range(1,m):
        if j==m//2 or (2*j)%m==0: continue
        lam_j_4=np.exp(2j*np.pi*j*n*ind[4%p]/(p-1))
        lhs=glam[j]*glam[(j+m//2)%m]
        rhs=(1/lam_j_4)*glam[(2*j)%m]*glam[m//2]
        errs.append(abs(lhs-rhs)/abs(lhs))
    print(f"p={p} n={n} m={m}: HD d=2 max rel err = {max(errs):.2e}  (relation {'EXACT' if max(errs)<1e-8 else 'FAILS'})")
    # E3 comparison: true J vs iid-phase null vs HD-constrained null
    chi_full=np.zeros(p); chi_full[1:]=np.where(ks%2==0,1.0,-1.0)
    ts=np.arange(p); om=(1-ts)%p
    J=np.zeros(m,dtype=complex)
    for j in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*j*n*ks/(p-1))
        J[j]=np.sum(lv[ts]*chi_full[om])
    Jm=J.copy(); Jm[0]=0
    def E3(v):
        Fv=np.fft.fft(v)
        return float(np.sum(np.abs(np.fft.ifft(Fv**3))**2))
    e_true=E3(Jm)
    rng=np.random.default_rng(0)
    absJ=np.abs(Jm)
    e_iid=np.mean([E3(absJ*np.exp(2j*np.pi*rng.random(m))*(np.arange(m)!=0)) for _ in range(trials)])
    print(f"   E3(true)/(6m^3q^3)={e_true/(6*m**3*p**3):.3f}   E3(iid-null)/(6m^3q^3)={e_iid/(6*m**3*p**3):.3f}   ratio true/iid={e_true/e_iid:.3f}")
for (p,n) in [(577,8),(3457,8),(4129,16),(5953,32)]:
    run(p,n)
