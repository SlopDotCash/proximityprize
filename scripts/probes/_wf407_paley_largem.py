import numpy as np
from sympy import isprime, primitive_root
import math

def gauss_periods_abs(p, n):
    g = primitive_root(p)
    m = (p-1)//n
    gm = pow(g, m, p)
    sub=[]; cur=1
    for j in range(n):
        sub.append(cur); cur=(cur*gm)%p
    sub=np.array(sub,dtype=np.int64)
    w=np.exp(2j*np.pi*np.arange(p)/p)
    bs=np.arange(1,p)
    eta=np.zeros(p-1,dtype=complex)
    for x in sub:
        eta+=w[(bs*x)%p]
    return np.abs(eta)

def Bval(p,n): return gauss_periods_abs(p,n).max()

# Test: does B <= 2 sqrt(n) (Ramanujan) hold as m GROWS, for fixed-ish n?
# And how does B/sqrt(n ln m) behave with large m?
print("=== LARGE INDEX m: is Cay(F_p, mu_n) still Ramanujan? ===")
print(f"{'n':>5} {'m':>8} {'p':>9} {'B':>9} {'2sqrt(n)':>9} {'sqrt(nlnm)':>10} {'B/2sqn':>7} {'B/sqnlnm':>9}")
import sympy
for n in [8,16,32]:
    # sweep m so that p=mn+1 is prime, m large
    cnt=0
    for m in range(2,4000):
        p=m*n+1
        if not isprime(p): continue
        if p>40000: break
        cnt+=1
        if cnt%7!=0 and m<3500: continue  # sample
        B=Bval(p,n)
        ram=2*math.sqrt(n)
        flo=math.sqrt(n*math.log(m))
        flag="  <-- > 2sqrt(n)!" if B>ram else ""
        print(f"{n:>5} {m:>8} {p:>9} {B:>9.3f} {ram:>9.3f} {flo:>10.3f} {B/ram:>7.3f} {B/flo:>9.3f}{flag}")
