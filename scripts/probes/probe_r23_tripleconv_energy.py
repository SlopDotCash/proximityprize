#!/usr/bin/env python3
"""R23: calibrate the triple-convolution energy of the Jacobi sequence (the machine-stated
r=3 object from _R22SexticConvolutionCollapse) against the Wick scale m^3 q^3.

Also validates the r22 collapse identity numerically:
  sum_{s!=0} |T(s)|^6 == (q-1) * sum_d |(J*J*J)(d)|^2   (exact)
with T(s) = sum_{j!=0} J_j lam_j(s), J_j = sum_t lam_j(t) chi(1-t), lam_j the dual family
of F*/mu_n, chi the quadratic character.
"""
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
    # chi = quadratic character; lam_j(g^k) = e(j n k/(p-1))
    ks=np.array([ind[a] for a in range(1,p)])
    chi_vals=np.where(ks%2==0,1.0,-1.0)   # chi on 1..p-1 (indexed by a-1)
    def lam_vec(j):
        v=np.zeros(p,dtype=complex)
        v[1:]=np.exp(2j*np.pi*j*n*ks/(p-1))
        return v
    # J_j = sum_t lam_j(t) chi(1-t)
    chi_full=np.zeros(p); chi_full[1:]=chi_vals
    J=np.zeros(m,dtype=complex)
    ts=np.arange(p)
    one_minus=(1-ts)%p
    for j in range(m):
        lv=lam_vec(j)
        J[j]=np.sum(lv[ts]*chi_full[one_minus])
    # tripleConv exactly as in Lean: selfConv(c)=sum_{j!=0, c-j!=0} J_j J_{c-j};
    # tripleConv(d) = sum_{j!=0} selfConv(d-j) J_j
    sc=np.zeros(m,dtype=complex)
    for c in range(m):
        for j in range(1,m):
            if (c-j)%m!=0:
                sc[c]+=J[j]*J[(c-j)%m]
    tc=np.zeros(m,dtype=complex)
    for d in range(m):
        for j in range(1,m):
            tc[d]+=sc[(d-j)%m]*J[j]
    E3=float(np.sum(np.abs(tc)**2))
    # T(s) and sextic moment (validate collapse)
    T=np.zeros(p,dtype=complex)
    for j in range(1,m):
        T+=J[j]*lam_vec(j)
    S6=float(np.sum(np.abs(T[1:])**6))
    lhs=S6; rhs=(p-1)*E3
    wick=15*(m**3)*(p**3)
    # also r=2 for reference
    E2=float(np.sum(np.abs(sc)**2))
    wick2=2*(m**2)*(p**2)  # 3!!=3? for complex Wick pairings of T^2: 2·(σ²)² per... report raw ratio
    print(f"p={p:>7} n={n:>3} m={m:>4} beta={math.log(p)/math.log(n):.2f} "
          f"collapse_err={abs(lhs-rhs)/max(lhs,1):.1e} E3/(m^3 q^3)={E3/((m**3)*(p**3)):.4f} "
          f"E2/(m^2 q^2)={E2/((m**2)*(p**2)):.4f}")

def primes_1mod(mm,count,start):
    out=[]; x=max(start-start%mm+1,mm+1)
    while len(out)<count and x<600000:
        if isprime(x): out.append(x)
        x+=mm
    return out

for n in (8,16,32):
    for beta in (2.5,3.0,4.0,4.6):
        for p in primes_1mod(2*n,1,int(n**beta)):
            if (p-1)//n < 400: run(p,n)
