import numpy as np
from sympy import primerange, isprime, primitive_root
import cmath, math

def gauss_periods(p, n):
    """Return array of eta_b for b=1..p-1 (constant on cosets). p prime, n | p-1.
       eta_b = sum_{x in mu_n} exp(2pi i b x / p)."""
    g = primitive_root(p)
    m = (p-1)//n
    # mu_n = <g^m> = {g^(m*j) mod p : j=0..n-1}
    sub = []
    cur = 1
    gm = pow(g, m, p)
    for j in range(n):
        sub.append(cur)
        cur = (cur*gm) % p
    sub = np.array(sub, dtype=np.int64)
    # eta_b for all b in 1..p-1
    w = np.exp(2j*np.pi*np.arange(p)/p)  # e_p(k) for k=0..p-1
    # eta_b = sum_x w[(b*x) mod p]
    bs = np.arange(1,p)
    # build matrix of (b*x) mod p ; n small, p moderate
    # vectorize over x
    eta = np.zeros(p-1, dtype=complex)
    for x in sub:
        eta += w[(bs*x) % p]
    return np.abs(eta)

def Bval(p,n):
    a = gauss_periods(p,n)
    return a.max()

print("=== REGIME A: FIXED INDEX m (positive-proportion subgroup, n grows) ===")
print(f"{'m':>6} {'n':>6} {'p':>9} {'B':>9} {'2sqrt(n)':>9} {'sqrt(n*lnm)':>11} {'B/2sqn':>7} {'B/sqnlnm':>9} {'B/sqrtn':>8}")
for m in [2,3,4,6,10]:
    for n in [10,30,60,120,250,500,1000]:
        # need prime p = m*n+1
        p = m*n+1
        if not isprime(p): continue
        B = Bval(p,n)
        ram = 2*math.sqrt(n)
        flo = math.sqrt(n*math.log(m)) if m>1 else float('nan')
        print(f"{m:>6} {n:>6} {p:>9} {B:>9.3f} {ram:>9.3f} {flo:>11.3f} {B/ram:>7.3f} {B/flo if flo==flo and flo>0 else float('nan'):>9.3f} {B/math.sqrt(n):>8.3f}")
