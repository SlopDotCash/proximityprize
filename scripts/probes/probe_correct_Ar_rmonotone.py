import math, cmath
from collections import Counter
def dblfact(k):
    r=1
    while k>1: r*=k; k-=2
    return r
def gen(p):
    for c in range(2,p):
        s=set(); v=1
        for _ in range(p-1):
            v=v*c%p; s.add(v)
        if len(s)==p-1: return c
def mun(n,p):
    g=gen(p); m=(p-1)//n
    return [pow(g,m*i,p) for i in range(n)]
def A_r_correct(n,p,r):
    # A_r = sum_{b!=0} |eta_b|^{2r}, eta_b = sum_{x in mu_n} e_p(bx)
    S=mun(n,p)
    tot=0.0
    for b in range(1,p):
        eta=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        tot += abs(eta)**(2*r)
    return tot
def pr(n,t):
    x=t+((1-t)%n)
    while True:
        if x>2 and x%2 and all(x%d for d in range(3,int(x**.5)+1,2)): return x
        x+=n
# CORRECT A_r for n=8, beta=4, p=4129, r=1..6. Wick = q(2r-1)!! n^r. ratio should be in (0,1) if wall holds.
n=8; p=pr(8,8**4)
print(f"n={n} p={p} beta={math.log(p)/math.log(n):.2f} ln q={math.log(p):.2f}")
print("CORRECT A_r = sum_{b!=0}|eta_b|^{2r};  ratio = A_r / [q(2r-1)!!n^r] (wall: <=1)")
for r in range(1,7):
    A=A_r_correct(n,p,r)
    W=p*dblfact(2*r-1)*n**r
    print(f"  r={r}: A_r={A:.3e}  Wick={W:.3e}  ratio={A/W:.4f}  {'FAILS >1' if A/W>1 else ''}")
