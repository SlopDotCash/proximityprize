import numpy as np
from sympy import isprime, primitive_root
import math

def gp_abs(p,n):
    g=primitive_root(p); m=(p-1)//n; gm=pow(g,m,p)
    sub=[]; cur=1
    for j in range(n):
        sub.append(cur); cur=(cur*gm)%p
    sub=np.array(sub,dtype=np.int64)
    w=np.exp(2j*np.pi*np.arange(p)/p); bs=np.arange(1,p)
    eta=np.zeros(p-1,dtype=complex)
    for x in sub: eta+=w[(bs*x)%p]
    return np.abs(eta)

def find_prime_fixed_m(m, ntarget):
    # find n near ntarget with m*n+1 prime
    for d in range(0, ntarget):
        for n in (ntarget+d, ntarget-d):
            if n<2: continue
            if isprime(m*n+1):
                return n, m*n+1
    return None,None

print("=== EVT law: B / sqrt(2 n ln m), fixed m, growing n (max of m real Gaussians) ===")
for m in [4,8,16,32]:
    logm=math.log(m)
    print(f"--- m={m} (ln m={logm:.3f}) ---")
    print(f"{'n':>6} {'p':>9} {'B':>9} {'B/sqrt(n lnm)':>13} {'B/sqrt(2n lnm)':>14}")
    for ntar in [50,100,200,400,800,1600]:
        n,p = find_prime_fixed_m(m,ntar)
        if n is None or p>120000: continue
        a=gp_abs(p,n); B=a.max()
        print(f"{n:>6} {p:>9} {B:>9.3f} {B/math.sqrt(n*logm):>13.4f} {B/math.sqrt(2*n*logm):>14.4f}")
