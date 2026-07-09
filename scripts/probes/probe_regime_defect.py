import numpy as np, math
from sympy import isprime, primitive_root, nextprime

# CORRECTED REGIME (issue comment 4700736246): m=(q-1)/n held CONSTANT as n grows.
# => mu_n positive-proportion, n=Theta(q). This is DIFFERENT from thin n=q^{1/beta}.
# Question for the moments-of-the-family route: in the CONSTANT-m regime, do the family
# moments (1/m)Sum|S(w)|^{2r} stay Gaussian-flat (ratio->1, descent works) or inflate (p-defect)?
# The Katz "moments of family" leading term is m*(Gaussian baseline); the ERROR is the defect.
# If defect dominates at small r, the family-moment route gives NOTHING beyond r=O(1).

def periods(p,n):
    g=primitive_root(p); m=(p-1)//n
    h=pow(g,m,p)
    mu=np.array([pow(h,i,p) for i in range(n)],dtype=np.int64)
    reps=np.array([pow(g,k,p) for k in range(m)],dtype=np.int64)
    M=(reps[:,None]*mu[None,:])%p
    eta=np.exp(2j*np.pi*M/p).sum(axis=1)
    return m,eta

def find_prime_const_m(n, m_target):
    # find prime p with (p-1)/n = m  i.e. p = n*m+1 prime, m near m_target
    for dm in range(0, 4000):
        for mm in (m_target+dm, m_target-dm):
            if mm<2: continue
            p=n*mm+1
            if isprime(p):
                return p, mm
    return None,None

print("=== CONSTANT-m regime (m~target fixed, n grows): does the family moment inflate? ===")
m_target=64
for n in [16,32,64,128,256,512]:
    p,mm=find_prime_const_m(n,m_target)
    if p is None: print(f"n={n}: no prime"); continue
    if p*n > 4e7:  # cap cost (p*n exps)
        # actually cost is m*n = mm*n, manageable; p can be big but we only do mm*n exps
        pass
    m,eta=periods(p,n)
    aeta=np.abs(eta); B=aeta.max(); rms=np.sqrt(np.mean(aeta**2))
    # family moments ratio vs Gaussian (2r-1)!! n^r
    ratios=[]
    for r in [2,3,4,5]:
        Er=np.mean(aeta**(2*r))   # (1/m) sum |eta|^{2r}
        gd=math.prod(range(1,2*r,2))*(n**r)
        ratios.append(Er/gd)
    print(f"n={n:4d} p={p:10d} m={m}: B/sqrt(n)={B/np.sqrt(n):.3f} B/sqrt(n ln m)={B/np.sqrt(n*np.log(m)):.3f}  rms/sqrt(n)={rms/np.sqrt(n):.3f}  defectRatio E_r/((2r-1)!!n^r) r=2..5: "+" ".join(f"{x:.3f}" for x in ratios))
