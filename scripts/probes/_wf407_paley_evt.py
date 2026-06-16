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

# Extreme-value-theory model: B = max over (m) approx-Gaussian complex eta with E|eta|^2 = n.
# For m iid complex Gaussians variance n (so |eta|^2 ~ Exp with mean n... actually |eta|~Rayleigh),
# max_{m} |eta| ~ sqrt(n * ln m). The constant: for m iid CN(0,n), max|eta| ~ sqrt(n ln m).
# Real eta_b are real (since sum over subgroup closed under inversion if -1 in mu_n) OR complex.
# Test: distinct coset-values count = m-? and distribution of |eta|.
print("=== EVT constant C = B / sqrt(n ln m), and variance check ===")
print(f"{'n':>4} {'m':>6} {'p':>8} {'B':>8} {'mean|eta|^2':>11} {'C=B/sqnlnm':>11} {'#distinct':>9}")
rows=[]
for (n,mrange) in [(6,range(50,700)),(12,range(20,400)),(20,range(10,250)),(30,range(5,170))]:
    best=[]
    for m in mrange:
        p=m*n+1
        if not isprime(p): continue
        if p>11000: break
        a=gp_abs(p,n)
        B=a.max(); meansq=(a**2).mean()
        C=B/math.sqrt(n*math.log(m))
        nd=len(set(np.round(a,6)))
        best.append((n,m,p,B,meansq,C,nd))
    # print the largest-m row for each n
    if best:
        for r in best[-3:]:
            print(f"{r[0]:>4} {r[1]:>6} {r[2]:>8} {r[3]:>8.3f} {r[4]:>11.3f} {r[5]:>11.4f} {r[6]:>9}")
