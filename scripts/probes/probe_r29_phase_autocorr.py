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
    for j in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*j*n*ks/(p-1))
        J[j]=np.sum(lv[ts]*chi_full[om])
    u=np.where(np.abs(J)>0, J/np.maximum(np.abs(J),1e-30), 0); u[0]=0
    # (1) linear-lag autocorrelations: A(t) = |sum_j u_{j+t} conj(u_j)|/m
    A=np.abs(np.fft.ifft(np.abs(np.fft.fft(u))**2))/m
    topA=sorted(range(1,m), key=lambda t:-A[t])[:3]
    # (2) the HD triple correlation: H = |sum_j u_j u_{j+m/2} conj(u_{2j})|/m  (exact resonance)
    if m%2==0:
        H=abs(sum(u[j]*u[(j+m//2)%m]*np.conj(u[(2*j)%m]) for j in range(1,m)))/m
    else:
        H=float('nan')
    # (3) generic doubling correlation D = |sum_j u_j^2 conj(u_{2j})|/m
    D=abs(sum(u[j]**2*np.conj(u[(2*j)%m]) for j in range(1,m)))/m
    print(f"p={p} n={n} m={m}: max linear-lag A(t)={A[topA[0]]:.3f}@t={topA[0]} (random ~ {1/math.sqrt(m):.3f})  HD-triple={H:.3f}  doubling D={D:.3f}")
for (p,n) in [(577,8),(3457,8),(4129,16),(5953,32)]:
    run(p,n)
