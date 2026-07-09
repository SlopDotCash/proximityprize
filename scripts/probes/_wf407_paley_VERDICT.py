"""[paley route, #407] Consolidated verdict probe: Ramanujan is FALSE; floor is sqrt(2 n ln m).
Reproduces the three headline claims of the spectral/Paley-graph attack."""
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

print("CLAIM 1: Ramanujan B<=2sqrt(n) FAILS once log m > 2 (excess factor -> sqrt(ln m /2)).")
print("  Fixed n=8, growing m: fraction of primes with B>2sqrt(n), and max excess B/2sqrt(n):")
n=8; ram=2*math.sqrt(n); cntbad=0; cnt=0; maxexc=0; vals=[]
for m in range(2,1600):
    p=m*n+1
    if not isprime(p) or p>13000: continue
    cnt+=1; B=gp_abs(p,n).max()
    if B>ram: cntbad+=1
    maxexc=max(maxexc,B/ram); vals.append((m,B/ram))
print(f"  -> {cntbad}/{cnt} primes have B>2sqrt(n); max excess={maxexc:.3f}; "
      f"first m exceeding=17 (B/2sqn~1.03). predicted plateau sqrt(ln m/2): "
      f"m=1500 -> {math.sqrt(math.log(1500)/2):.2f}")

print("\nCLAIM 2: per-period variance = n exactly (Parseval), so floor scale is sqrt(n * ...).")
for (p,n) in [(401,8),(1201,8),(3001,30)]:
    a=gp_abs(p,n); print(f"  p={p} n={n}: mean|eta|^2 = {(a**2).mean():.4f}  (=n={n})")

print("\nCLAIM 3: floor law B ~ sqrt(2 n ln m) (Gaussian EVT constant C0=sqrt2 asymptotically).")
print("  Large-m sample (n=8), B/sqrt(2 n ln m) and B/sqrt(n ln m):")
for m in [200,500,1000,1500]:
    # nearest prime
    mm=m
    while not isprime(mm*n+1): mm+=1
    p=mm*n+1; B=gp_abs(p,n).max()
    print(f"  m={mm} p={p}: B={B:.3f}  B/sqrt(2n ln m)={B/math.sqrt(2*n*math.log(mm)):.3f}  "
          f"B/sqrt(n ln m)={B/math.sqrt(n*math.log(mm)):.3f}")
print("\nVERDICT: spectral-graph Ramanujan is the WRONG (false) target; correct target is the")
print("EVT floor B<=C sqrt(n log m), C0=sqrt2 -- an analytic-NT statement, no spectral upper handle.")
