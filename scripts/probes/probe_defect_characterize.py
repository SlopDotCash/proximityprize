import numpy as np, math
from sympy import isprime, primitive_root, factorint

# Characterize WHEN the family-moment defect turns on in the constant-m regime, and tie it to
# the Katz conductor. Hypothesis: defect = #{short sparse +-relations of n-th roots vanishing
# mod p} = the cyclotomic-norm collision. The Katz "error term" of the family-moment integral
# IS this defect. Conductor barrier reappears as: defect controlled only when (2r)^{phi(n)} < p,
# i.e. r < log(p)/(phi(n) log(2r)) = O(log p / n) -> O(1) at n=Theta(q). 

def periods(p,n):
    g=primitive_root(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    reps=np.array([pow(g,k,p) for k in range(m)],dtype=np.int64)
    M=(reps[:,None]*mu[None,:])%p
    eta=np.exp(2j*np.pi*M/p).sum(axis=1)
    return m,eta

def defect_table(p,n,maxr=6):
    m,eta=periods(p,n)
    aeta=np.abs(eta)
    out=[]
    for r in range(2,maxr+1):
        Er=np.mean(aeta**(2*r))
        gd=math.prod(range(1,2*r,2))*(n**r)
        out.append((r,Er/gd))
    return m,aeta.max(),out

# Many primes for n=128 to see defect distribution. p=128*m+1, m near 60.
print("=== n=128, scan m to find when family moment inflates (defect>1 at r=2) ===")
n=128
cnt_clean=0; cnt_defect=0
for m in range(48, 90):
    p=n*m+1
    if not isprime(p): continue
    mm,B,tab=defect_table(p,n,maxr=4)
    r2=tab[0][1]; r3=tab[1][1]; r4=tab[2][1]
    flag="  <== DEFECT (r2>1)" if r2>1.0 else ""
    if r2>1.0: cnt_defect+=1
    else: cnt_clean+=1
    print(f"  p={p:7d} m={m}: B/sqrt(n ln m)={B/np.sqrt(n*np.log(mm)):.3f} defect r2={r2:.3f} r3={r3:.3f} r4={r4:.3f}{flag}")
print(f"clean(r2<=1)={cnt_clean} defect(r2>1)={cnt_defect}")
