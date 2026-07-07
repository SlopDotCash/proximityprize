#!/usr/bin/env python3
"""
S6 THRESHOLD-LAW probe (#444) -- the DECISIVE test, FAST version (binary search + FFT energy).

tau_r(n) := the threshold prime above which spur_r(p) = E_r^{Fp} - E_r^{c0} = 0.
spur is one-sided (>=0) and (empirically) monotone-vanishing in p for p=1 mod n, so we
BINARY-SEARCH the threshold over the index of primes p=1 mod n, using a fast FFT energy.

beta*(n,r) = log_n(tau_r). Deligne-uniform => beta* bounded; wall => beta* ~ (r+3)/2.

FFT energy reliability: E_r is an integer; we verify |round(val)-val| is tiny and cross-check
small cases vs exact convolution. We keep r small enough (<=6) and p moderate that float64 FFT
of |T|^{2r} stays well within integer resolution.
"""
import math
import numpy as np
from collections import defaultdict

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d,s=m-1,0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def primitive_root(p):
    phi=p-1; m=phi; fac=[]; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=x*h%p
    assert len(S)==n
    return sorted(S)

def energy_fft(p,S,r):
    ind=np.zeros(p);
    for x in S: ind[x]=1.0
    T=np.fft.rfft(ind)         # real input -> half spectrum, but we need all b; use full via fft
    # use full fft for correctness of sum over all b
    Tf=np.fft.fft(ind)
    pw=(np.abs(Tf)**2)**r
    val=pw.sum()/p
    iv=int(round(val))
    err=abs(val-iv)
    return iv, err

def energy_conv(p,S,r):
    dist=defaultdict(int); dist[0]=1
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for x in S: nd[(s+x)%p]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def root_vec(n,k):
    half=n//2; k%=n; v=[0]*half
    if k<half: v[k]=1
    else: v[k-half]=-1
    return tuple(v)

def char0(n,r):
    half=n//2; dist=defaultdict(int); dist[tuple([0]*half)]=1
    rv=[root_vec(n,k) for k in range(n)]
    for _ in range(r):
        nd=defaultdict(int)
        for vec,c in dist.items():
            for w in rv:
                nv=tuple(vec[t]+w[t] for t in range(half)); nd[nv]+=c
        dist=nd
    return sum(c*c for c in dist.values())

def nth_prime_1modn(n, idx):
    """idx-th prime (1-based) congruent to 1 mod n."""
    cnt=0; p=1+n
    while True:
        if is_prime(p):
            cnt+=1
            if cnt==idx: return p
        p+=n

def prime_1modn_above(n, lo):
    p = lo + ((1-lo)%n)
    if p<lo: p+=n
    if p<2: p=1+n
    while not is_prime(p): p+=n
    return p

# sanity: FFT vs conv
print("FFT-vs-conv sanity:")
for (p,n,r) in ((257,16,3),(1153,32,4),(7681,16,5)):
    S=mu_n(p,n); a,err=energy_fft(p,S,r); b=energy_conv(p,S,r)
    print(f"  p={p} n={n} r={r}: fft={a}(err {err:.2e}) conv={b}  {'OK' if a==b else 'MISMATCH'}")

print("\n"+"="*100)
print("THRESHOLD: smallest prime p=1modn with spur=0, scanning UP (spur one-sided, find last nonzero)")
print("="*100)

def threshold_betastar(n, r, pmax_beta=6.0, max_primes=1500):
    c0=char0(n,r)
    pmax=int(n**pmax_beta)
    last_nonzero=0; first_zero=None; checked=0
    p=1+n
    while p<=pmax and checked<max_primes:
        if is_prime(p):
            checked+=1
            S=mu_n(p,n)
            Ep,err=energy_fft(p,S,r)
            if err>0.3:  # FFT unreliable -> fall back to conv (rare)
                Ep=energy_conv(p,S,r)
            spur=Ep-c0
            if spur!=0:
                last_nonzero=p
        p+=n
    tau=last_nonzero
    bstar=math.log(tau)/math.log(n) if tau>0 else 0.0
    return tau,bstar,checked

results={}
for n in (8,16,32):
    print(f"\n--- n={n} ---")
    for r in range(2,7):
        # limit prime size so FFT array (length p) and #primes stay feasible
        # for n=32 cap beta at ~5 (p<=32^5=3.3e7 too big for many FFTs); use moderate cap
        if n==32:
            cap=5.0; mp=400
        elif n==16:
            cap=6.0; mp=1200
        else:
            cap=6.5; mp=2500
        tau,bstar,chk=threshold_betastar(n,r,cap,mp)
        results[(n,r)]=(tau,bstar)
        flag=""
        if bstar>=cap-0.05: flag=" (>=cap! true tau higher)"
        print(f"  r={r}: tau_r={tau:>10d}  beta*={bstar:.3f}   [(r+3)/2={(r+3)/2:.1f}] checked={chk}{flag}")

print("\n"+"="*100)
print("beta*(n,r) TABLE  vs  (r+3)/2:")
print("="*100)
print(f"{'r':>3} | " + " | ".join(f"n={n}".rjust(9) for n in (8,16,32)) + " |  (r+3)/2  | r_max@b4=2b-3")
for r in range(2,7):
    row=f"{r:>3} | "
    for n in (8,16,32):
        b=results.get((n,r),(0,0))[1]
        row+=f"{b:9.3f} | "
    rmax_ok = "OK" if (r+3)/2 <= 4 else "FAIL@b4"
    row+=f"   {(r+3)/2:.1f}    |  {rmax_ok}"
    print(row)
print("\nKEY: at prize beta=4, transfer requires (r+3)/2 <= 4 i.e. r <= 5. r>5 needs p>n^4 => FAILS.")
print("If beta* tracks (r+3)/2 (grows with r), the Betti/defect grows with n  =>  REDUCES TO WALL.")
