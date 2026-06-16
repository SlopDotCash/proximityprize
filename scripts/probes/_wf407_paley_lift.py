import numpy as np
from sympy import isprime, primitive_root
import math

# The index-m covering / lift structure:
# Gauss periods are eta_j = sum_{a=0}^{n-1} zeta_p^{g^{m*a + j}}, j=0..m-1.
# Equivalent (DFT identity from prompt): eta_b = (1/m)[-1 + sum_{i=1}^{m-1} psi(b)^{-i} tau(psi^i)],
# |tau|=sqrt(p). So (eta_b + 1/m... ) the m Gauss periods are the m-point DFT of the
# (m-1) unimodular Gauss-sum phases a_i = tau(psi^i)/sqrt(p).
# B ~ (sqrt(p)/m) * ||DFT(a)||_inf.  Test the DFT-of-unimodular-phases model DIRECTLY.

def gp_and_phases(p,n):
    g=primitive_root(p); m=(p-1)//n; gm=pow(g,m,p)
    sub=[]; cur=1
    for j in range(n):
        sub.append(cur); cur=(cur*gm)%p
    sub=np.array(sub,dtype=np.int64)
    w=np.exp(2j*np.pi*np.arange(p)/p); bs=np.arange(1,p)
    eta=np.zeros(p-1,dtype=complex)
    for x in sub: eta+=w[(bs*x)%p]
    B=np.abs(eta).max()
    return B,m

# KEY SPECTRAL TEST: does the "lift" (covering) give Ramanujan of the BASE times sqrt(deg of cover)?
# A clean spectral inequality reachable: for ANY n-regular graph on N vertices,
# lambda_2 <= n (trivial), and >= 2sqrt(n-1)-o(1) (Alon-Boppana, a LOWER bound).
# The expander-mixing/Cheeger gives NO sub-trivial upper bound without arithmetic input.
# Verify: is there ANY graph-theoretic monotonicity B(m) as m grows for fixed n?
print("=== B vs m (fixed n) growth law: pure power-of-log? ===")
for n in [6,8,12,16]:
    data=[]
    for m in range(2,3000):
        p=m*n+1
        if not isprime(p): continue
        if p>22000: break
        B,mm=gp_and_phases(p,n)
        data.append((m,B))
    if len(data)<8: continue
    # fit B^2 = a*n*ln(m) + c  -> slope a, also B^2/n vs ln m
    ms=np.array([d[0] for d in data],dtype=float)
    Bs=np.array([d[1] for d in data],dtype=float)
    y=Bs**2/n
    x=np.log(ms)
    A=np.vstack([x,np.ones_like(x)]).T
    slope,intercept=np.linalg.lstsq(A,y,rcond=None)[0]
    print(f"n={n:>3}: B^2/n = {slope:.3f}*ln(m) + {intercept:.3f}   (#pts={len(data)}, m up to {int(ms.max())})  -> C^2_eff={slope:.3f}")
