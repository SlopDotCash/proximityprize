import numpy as np, math
from sympy import isprime, primitive_root

# THE MOMENT-METHOD CEILING in the family-moment route, corrected regime.
# Best sup bound from moments up to depth R: min_{r<=R} (m * M_r)^{1/2r}, M_r=(1/m)sum|S|^{2r}.
# If the family moment is Gaussian to depth R (M_r ~ (2r-1)!! n^r), the bound at optimal r~ln m
# reaches ~sqrt(2 n ln m). The DEFECT caps the usable R. Measure the achievable bound vs depth
# in the constant-m regime, contrasting a CLEAN prime and a DEFECT prime.

def periods(p,n):
    g=primitive_root(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    reps=np.array([pow(g,k,p) for k in range(m)],dtype=np.int64)
    M=(reps[:,None]*mu[None,:])%p
    eta=np.exp(2j*np.pi*M/p).sum(axis=1)
    return m,eta

def moment_bound_curve(p,n,maxr=14):
    m,eta=periods(p,n)
    aeta=np.abs(eta); B=aeta.max()
    # M_r = (1/m) sum |eta|^{2r}; sup-bound from depth r: (m * M_r)^{1/2r}
    curve=[]
    for r in range(1,maxr+1):
        Mr=np.mean(aeta**(2*r))
        bnd=(m*Mr)**(1.0/(2*r))
        gd=math.prod(range(1,2*r,2))*(n**r)
        curve.append((r, bnd, Mr/gd))
    best=min(c[1] for c in curve)
    return m,B,curve,best

# CLEAN prime n=128 p=7681 (defect r2=0.75) vs DEFECT prime p=7937 (r2=1.15)
for (p,n,label) in [(7681,128,"CLEAN"),(7937,128,"DEFECT"),(11393,128,"DEFECT2")]:
    m,B,curve,best=moment_bound_curve(p,n,maxr=14)
    tgt=np.sqrt(n*np.log(m)); tgt2=np.sqrt(2*n*np.log(m))
    print(f"\n{label} p={p} n={n} m={m}: true B={B:.2f}  sqrt(n ln m)={tgt:.2f} sqrt(2n ln m)={tgt2:.2f}")
    print(f"  best moment-bound over r<=14 = {best:.2f}  (best/B={best/B:.2f})")
    for (r,bnd,dr) in curve:
        mark=" *defect>1" if dr>1.0 else ""
        print(f"   r={r:2d}: sup-bound={bnd:7.2f}  defect E_r/Gauss={dr:.3f}{mark}")
