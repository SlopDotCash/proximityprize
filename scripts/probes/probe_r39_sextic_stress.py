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
def run(p,n,ntrials=24):
    g=prim_root(p); m=(p-1)//n; N=p-1
    pw=[1]*N
    for k in range(1,N): pw[k]=pw[k-1]*g%p
    ind={pw[k]:k for k in range(N)}
    f0=np.array([ (1.0 if ind[(1-pw[k])%p]%2==0 else -1.0) if (1-pw[k])%p!=0 else 0.0 for k in range(N)],dtype=complex)
    ar=np.arange(N)
    def tw(t): return f0*np.exp(2j*np.pi*t*n*ar/N)
    def mconv(A,B): return np.fft.ifft(np.fft.fft(A)*np.fft.fft(B))
    rng=np.random.default_rng(7)
    worst=0; wshape=None
    for _ in range(ntrials):
        a,b,ap,bp=rng.integers(0,m,4)
        t=int(rng.integers(1,m))
        ku=int(rng.integers(0,N))
        A=mconv(mconv(tw(0),tw(a)),tw(b)); B=mconv(mconv(tw(0),tw(ap)),tw(bp))
        S=np.sum(np.roll(A,-ku)*np.conj(B)*np.exp(2j*np.pi*t*n*ar/N))
        r=abs(S)/p**2.5
        if r>worst: worst=r; wshape=(int(a),int(b),int(ap),int(bp),t,ku)
    # also degenerate-shape stress: a=b=a'=b'=0 (pure cubes)
    A=mconv(mconv(tw(0),tw(0)),tw(0))
    for t in range(1,min(m,6)):
        for ku in (0,1,N//3):
            S=np.sum(np.roll(A,-ku)*np.conj(A)*np.exp(2j*np.pi*t*n*ar/N))
            r=abs(S)/p**2.5
            if r>worst: worst=r; wshape=('cube',t,ku)
    print(f"p={p:>7} n={n:>3} m={m:>5} beta={math.log(p)/math.log(n):.2f}: worst|S|/q^2.5={worst:.3f}  shape={wshape}")
    return worst
w=0
for (p,n) in [(577,8),(3457,8),(32801,8),(4129,16),(65537,16),(1153,32),(5953,32),(33409,32)]:
    w=max(w,run(p,n))
print(f"GLOBAL worst/q^2.5 = {w:.3f}  (C=4 margin: {4/w:.1f}x)")
