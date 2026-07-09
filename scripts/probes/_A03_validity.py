import math, sys
import numpy as np
from numpy import i0
from sympy import isprime, primitive_root

def gauss_abs(p,n):
    g=int(primitive_root(p)); step=(p-1)//n
    x=pow(g,step,p); cur=1; mu=[]
    for _ in range(n): mu.append(cur); cur=cur*x%p
    ind=np.zeros(p); ind[mu]=1.0
    return np.abs(np.fft.fft(ind))

def find_prime(n,beta):
    t=n**beta; p=((int(t)//n)+1)*n+1
    while not isprime(p): p+=n
    return p

O=open("scripts/probes/_A03_validity.txt","w",encoding="utf-8")
def w(s): O.write(s+"\n"); O.flush()
w("Per (n,p): y_valid = largest y with char-0 cosh ratio<=1.02;  y_opt = char-0 bound minimizer.")
w("If y_opt > y_valid, the char-0 saddle bound is EVALUATED OUTSIDE its validity region (a FICTION).")
for n in [16,32,64]:
    for beta in [3.0,4.0]:
        p=find_prime(n,beta)
        if p>4_500_000:
            w(f"n={n} beta={beta} p={p} skip(large)"); continue
        A=gauss_abs(p,n)
        yvalid=0.0
        for k in range(1,400):
            y=0.01*k
            lhs=float(np.sum(np.cosh(A*y)))
            logrhs=math.log(p)+(n/2)*math.log(float(i0(2*y)))
            if abs(math.log(lhs)-logrhs) < math.log(1.02): yvalid=y
            else: break
        best=1e18;yopt=None
        for k in range(1,2000):
            y=0.005*k
            logz=math.log(p)+(n/2)*math.log(float(i0(2*y)))
            ac=logz+math.log1p(math.sqrt(max(0,1-math.exp(-2*logz))))
            v=ac/y
            if v<best:best=v;yopt=y
        flag="OUTSIDE validity (FICTION)" if yopt>yvalid else "inside validity"
        w(f"n={n:3d} beta={beta} p={p:8d}: y_valid={yvalid:.2f}  y_opt={yopt:.2f}  -> {flag}   char0bound={best:.2f} floor={math.sqrt(2*n*math.log(p/n)):.2f}")
O.close()
print("done")
