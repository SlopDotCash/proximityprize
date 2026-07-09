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

# LIFT/COVERING: mu_n subset mu_{2n} subset ... subset mu_{2^a*n0}.
# Cay(F_q, mu_{2n}) "lifts" Cay(F_q, mu_n): does B(mu_{2n}) relate to B(mu_n)?
# Spectral expectation if it were a clean 2-cover: B_lift in {+-(sum of base eigs)} -- no upper control.
# Probe: B(n) along a 2-power tower n=2^k * n0 inside a fixed prime p.
print("=== TOWER B(mu_{2^k}) inside fixed p: does lift give upper control? ===")
for p in [7681, 12289, 40961, 65537]:  # NTT primes, p-1 highly 2-divisible
    if not isprime(p): continue
    # factor out powers of 2 from p-1
    e=0; t=p-1
    while t%2==0: t//=2; e+=1
    print(f"p={p}, p-1=2^{e}*{t}")
    print(f"  {'n=2^k':>8} {'m':>7} {'B':>9} {'2sqrt(n)':>9} {'sqrt(2n lnm)':>12} {'B/2sqn':>7} {'B/sqrt(2nlnm)':>13}")
    for k in range(1, e+1):
        n=2**k
        if (p-1)%n!=0: continue
        m=(p-1)//n
        a=gp_abs(p,n); B=a.max()
        ram=2*math.sqrt(n); evt=math.sqrt(2*n*math.log(m))
        print(f"  {n:>8} {m:>7} {B:>9.3f} {ram:>9.3f} {evt:>12.3f} {B/ram:>7.3f} {B/evt:>13.3f}")
