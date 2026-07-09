import numpy as np
from sympy import isprime, primitive_root

# Vectorized: eta_b for all cosets via FFT. mu_n = <g^m>. 
# eta_{g^k} = sum_{i=0}^{n-1} e_p(g^{k+ m i})  -- but easier: build period over all b in F_p* by DFT.
# Actually fastest: the m periods are the DFT of the indicator of mu_n. 
# Cay(F_p,mu_n) eigenvalues = { sum_{x in mu_n} omega_p^{b x} : b }, distinct values = m of them (cosets).
def periods(p,n):
    g=primitive_root(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    # coset reps g^k, k=0..m-1
    reps=np.array([pow(g,k,p) for k in range(m)],dtype=np.int64)
    ph=np.exp(2j*np.pi/p)
    # eta_k = sum_x exp(2pi i reps_k*mu_x/p)
    # outer product (reps_k*mu_x mod p)
    M=(reps[:,None]*mu[None,:])%p
    eta=np.exp(2j*np.pi*M/p).sum(axis=1)
    return m,eta

def analyze(p,n,maxr=8):
    m,eta=periods(p,n)
    # S family = m*eta+1 (verified identity); absS = |m eta +1|
    S=m*eta+1.0
    absS=np.abs(S)/np.sqrt(p)  # = |S(w)| in unimodular normalization
    # Equivalently B-object: |eta| ; B=max|eta|; rms=sqrt(n)
    aeta=np.abs(eta)
    B=aeta.max(); rms=np.sqrt(np.mean(aeta**2))
    out={'p':p,'n':n,'m':m,'B':B,'rms_eta':rms,'B/sqrtn':B/np.sqrt(n),
         'B/sqrt(n ln m)':B/np.sqrt(n*np.log(m))}
    # family moments of |S|: Katz "moments of family" = (1/m) sum |S(w)|^{2r}
    fm=[]
    for r in range(1,maxr+1):
        Mr=np.mean(absS**(2*r))
        fm.append((r,Mr))
    out['fm']=fm; out['absS']=absS
    return out

prs=[(193,16),(1153,16),(12289,16),(7681,32),(40961,32),(786433,64),(12289,64),(40961,64),(163841,128)]
import math
for (p,n) in prs:
    if not isprime(p) or (p-1)%n: continue
    o=analyze(p,n,maxr=6)
    print(f"\np={o['p']} n={o['n']} m={o['m']}: B={o['B']:.3f} B/sqrt(n)={o['B/sqrtn']:.3f} B/sqrt(n ln m)={o['B/sqrt(n ln m)']:.3f}")
    absS=o['absS']; m=o['m']
    sup=absS.max(); rmsS=np.sqrt(np.mean(absS**2))
    print(f"   |S| family (S=m eta+1)/sqrt p: sup={sup:.2f} rms={rmsS:.3f} sup/rms={sup/rmsS:.2f}")
    for (r,Mr) in o['fm']:
        # moment-method sup estimate: (m * Mr)^{1/2r} should -> sup as r grows
        est=(m*Mr)**(1.0/(2*r))
        gp=math.prod(range(1,2*r,2))  # (2r-1)!!
        print(f"     r={r}: (1/m)Sum|S|^2r={Mr:.3e}  (m*Mr)^(1/2r)={est:.3f}  ratio Mr/((rms^2)^r (2r-1)!!)={Mr/((rmsS**2)**r*gp):.3f}")
