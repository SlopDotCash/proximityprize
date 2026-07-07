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
    g=prim_root(p); m=(p-1)//n; N=p-1
    # exponent-coordinate tables: value at g^k
    pw=[1]*N
    for k in range(1,N): pw[k]=pw[k-1]*g%p
    # chi quadratic: chi(g^k)=(-1)^k ; f0[k] = chi(1 - g^k)
    ind={pw[k]:k for k in range(N)}
    def chi(a):
        a%=p
        if a==0: return 0.0
        return 1.0 if ind[a]%2==0 else -1.0
    f0=np.array([chi((1-pw[k])%p) for k in range(N)],dtype=complex)
    def lamvec(t):  # λ_t(g^k) = e(t n k/(q−1))
        return np.exp(2j*np.pi*t*n*np.arange(N)/N)
    def tw(t): return f0*lamvec(t)
    def mconv(A,B):  # cyclic convolution on Z/N
        return np.fft.ifft(np.fft.fft(A)*np.fft.fft(B))
    def tripleTW(a,b):
        return mconv(mconv(tw(0),tw(a)),tw(b))
    rng=np.random.default_rng(1)
    worst=0
    for _ in range(6):
        a,b,ap,bp,t=rng.integers(1,m,5)
        ku=int(rng.integers(1,N))
        A=tripleTW(a,b); B=tripleTW(ap,bp)
        # S = Σ_k A[k+ku]·conj(B[k])·λ_t(g^k)
        S=np.sum(np.roll(A,-ku)*np.conj(B)*lamvec(t))
        worst=max(worst,abs(S))
    print(f"p={p:>6} n={n:>3} m={m:>4}: worst|S|/q^2.5={worst/p**2.5:.3f}  /q^3={worst/p**3:.5f}  max|A|/q={float(np.max(np.abs(A)))/p:.3f}")
for (p,n) in [(577,8),(1153,32),(4129,16),(3457,8)]:
    run(p,n)
