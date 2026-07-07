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
    if m%3==0: return  # keep 3 invertible for the clean t-parametrization
    ind={}; x=1
    for k in range(p-1): ind[x]=k; x=x*g%p
    ks=np.array([ind[a] for a in range(1,p)])
    chi=np.zeros(p); chi[1:]=np.where(ks%2==0,1.0,-1.0)
    ts=np.arange(p); om=(1-ts)%p
    J=np.zeros(m,dtype=complex)
    for jj in range(m):
        lv=np.zeros(p,dtype=complex); lv[1:]=np.exp(2j*np.pi*jj*n*ks/(p-1))
        J[jj]=np.sum(lv[ts]*chi[om])
    Jm=J.copy(); Jm[0]=0
    tc=np.fft.ifft(np.fft.fft(Jm)**3)
    E3=float(np.sum(np.abs(tc)**2))
    jv=np.arange(m)
    inv3=pow(3,-1,m)
    # t = inv3*(a'+b'-a-b). t=0 class ⟺ a+b ≡ a'+b'. Sum corr over the FULL t=0 class exactly:
    # S0 = Σ_{a,b,a',b': a+b=a'+b'} Σ_j J_j J_{j+a} J_{j+b} conj(J_j J_{j+a'} J_{j+b'})
    #    = Σ_j Σ_{s} |Σ_{a+b=s} J_{j+a}J_{j+b}|² ·|J_j|²  -- factor per (j, s=a+b)!
    S0=0.0
    for j in range(m):
        # P_j(s) = Σ_{a+b=s} J_{j+a}J_{j+b} = cyclic self-conv of the rotated sequence
        R=np.roll(Jm,-j)
        P=np.fft.ifft(np.fft.fft(R)**2)
        S0+=float(np.abs(Jm[j])**2*np.sum(np.abs(P)**2))
    print(f"p={p:>6} n={n:>3} m={m:>4}: E3={E3:.3e}  S0(t=0 class)={S0:.3e}  S0/E3={S0/E3:.3f}  offclass=(E3-S0)/E3={1-S0/E3:+.3f}")
for (p,n) in [(577,8),(1153,32),(4129,16),(3457,8)]:
    run(p,n)
