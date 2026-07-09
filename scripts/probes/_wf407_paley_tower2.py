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
print("=== TOWER B(mu_{2^k}) inside fixed NTT prime: lift gives upper control? ===")
for p in [7681, 12289]:  # smaller NTT primes
    e=0; t=p-1
    while t%2==0: t//=2; e+=1
    print(f"p={p}, p-1=2^{e}*{t}")
    print(f"  {'n=2^k':>8} {'m':>7} {'B':>9} {'2sqrt(n)':>9} {'sqrt(2n lnm)':>12} {'B/2sqn':>7} {'B/sqrt(2nlnm)':>13}")
    for k in range(1, min(e,11)+1):
        n=2**k; m=(p-1)//n
        a=gp_abs(p,n); B=a.max()
        ram=2*math.sqrt(n); evt=math.sqrt(2*n*math.log(m))
        print(f"  {n:>8} {m:>7} {B:>9.3f} {ram:>9.3f} {evt:>12.3f} {B/ram:>7.3f} {B/evt:>13.3f}")
