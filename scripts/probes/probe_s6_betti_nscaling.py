#!/usr/bin/env python3
"""
S6 DECISIVE probe (#444): does the spur reveal a Betti number that GROWS with n (= the wall)
or stays n-independent (= genuine Deligne route)?

char-p E_r via the EXACT exponential-sum identity, computed with numpy FFT (fast, O(p log p)):
  E_r^{Fp} = (1/p) sum_{b=0}^{p-1} |T_b|^{2r},  T_b = sum_{x in mu_n} e_p(b x).
T_b = DFT of the indicator vector of mu_n (length p). E_r is an integer; we round.
char-0 E_r exact via cyclotomic coordinates (n=2^mu). spur = E_Fp - E_c0 >= 0.
"""
import math
import numpy as np
from collections import defaultdict

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def find_prime_1_mod_n(n, lo):
    p = lo + ((1 - lo) % n)
    if p < lo: p += n
    while not is_prime(p): p += n
    return p

def primitive_root(p):
    phi = p-1; m=phi; factors=[]; d=2
    while d*d<=m:
        if m%d==0:
            factors.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.append(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in factors): return g

def mu_n(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=x*h%p
    assert len(S)==n
    return sorted(S)

def energy_r_charp_fft(p, S, r):
    """E_r = (1/p) sum_b |T_b|^{2r}, T_b = DFT of indicator(S). Exact integer (rounded)."""
    ind = np.zeros(p, dtype=np.float64)
    for x in S: ind[x] = 1.0
    T = np.fft.fft(ind)            # T[b] = sum_x e^{-2pi i b x/p}; |T| same as e^{+...}
    powr = (np.abs(T)**2)**r
    val = powr.sum()/p
    return int(round(val))

def root_vec(n, k):
    half = n//2; k %= n
    v = [0]*half
    if k < half: v[k]=1
    else: v[k-half]=-1
    return tuple(v)

def char0_energy_cyclo(n, r):
    half = n//2
    dist = defaultdict(int); dist[tuple([0]*half)] = 1
    rv = [root_vec(n,k) for k in range(n)]
    for _ in range(r):
        nd = defaultdict(int)
        for vec,c in dist.items():
            for w in rv:
                nv = tuple(vec[t]+w[t] for t in range(half)); nd[nv]+=c
        dist = nd
    return sum(c*c for c in dist.values())

def wick(n,r):
    dd=1
    for k in range(1,2*r,2): dd*=k
    return dd*(n**r)

# verify FFT char-p matches direct conv on a small case
def energy_r_direct(p,S,r):
    dist=defaultdict(int); dist[0]=1
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for x in S: nd[(s+x)%p]+=c
        dist=nd
    return sum(c*c for c in dist.values())

print("FFT-vs-direct sanity (must match exactly):")
for (p,n,r) in ((257,16,3),(1153,32,3)):
    S=mu_n(p,n)
    a=energy_r_charp_fft(p,S,r); b=energy_r_direct(p,S,r)
    print(f"  p={p} n={n} r={r}: fft={a} direct={b}  {'OK' if a==b else 'MISMATCH'}")

print("\nSANITY char-0 closed forms (E_2=3n^2-3n, E_3=15n^3-45n^2+40n):")
for n in (8,16,32,64):
    e2=char0_energy_cyclo(n,2); e3=char0_energy_cyclo(n,3)
    print(f"  n={n}: E_2={e2}({3*n*n-3*n})  E_3={e3}({15*n**3-45*n**2+40*n})")

print("\n"+"="*100)
print("S6 DECISIVE: n-scaling of spur at FIXED beta~4, FIXED r  (does Betti grow with n?)")
print("="*100)
for r in (3, 4):
    print(f"\n--- r={r}, beta~4 (p = smallest prime =1 mod n above n^4) ---")
    rows=[]
    for n in (8,16,32,64,128,256):
        p = find_prime_1_mod_n(n, n**4)
        if p > 8*10**7: print(f"  n={n}: p={p} too big for FFT mem, skip"); continue
        S=mu_n(p,n)
        Ep=energy_r_charp_fft(p,S,r); c0=char0_energy_cyclo(n,r)
        spur=Ep-c0; w=wick(n,r); beta=math.log(p)/math.log(n)
        rows.append((n,p,beta,Ep,c0,spur,w))
        srel=spur/c0 if c0 else float('nan')
        print(f"  n={n:3d} p={p:>10d} beta={beta:.3f}  E_Fp={Ep:>18d} E_c0={c0:>18d} "
              f"spur={spur:>14d}  spur/E_c0={srel:.6f}  K(Fp/Wick)={(Ep/w)**(1/r):.4f}")
    # spur n-exponent
    sp=[(n,spur) for (n,_,_,_,_,spur,_) in rows if spur>0]
    if len(sp)>=2:
        print("    spur n-exponent alpha (log-log consecutive):")
        for i in range(1,len(sp)):
            alpha=(math.log(sp[i][1])-math.log(sp[i-1][1]))/(math.log(sp[i][0])-math.log(sp[i-1][0]))
            print(f"       n={sp[i-1][0]}->{sp[i][0]}: alpha={alpha:.3f}")
    # also: E_c0 n-exponent for comparison (main term ~ n^r so alpha~r expected)
    c0s=[(n,c0) for (n,_,_,_,c0,_,_) in rows]
    print("    (compare) E_c0 n-exponent (should be ~r):")
    for i in range(1,len(c0s)):
        a=(math.log(c0s[i][1])-math.log(c0s[i-1][1]))/(math.log(c0s[i][0])-math.log(c0s[i-1][0]))
        print(f"       n={c0s[i-1][0]}->{c0s[i][0]}: alpha={a:.3f}")

print("\n"+"="*100)
print("S6: r-ladder at fixed n, beta~4.  K(Fp/c0) bounded/antitone? (the 4^r question)")
print("="*100)
for n in (8,16,32):
    p=find_prime_1_mod_n(n, n**4)
    if p>8*10**7: print(f"n={n} skip"); continue
    S=mu_n(p,n); beta=math.log(p)/math.log(n)
    print(f"\n--- n={n}, p={p}, beta={beta:.3f} ---")
    for r in range(2,10):
        Ep=energy_r_charp_fft(p,S,r); c0=char0_energy_cyclo(n,r)
        spur=Ep-c0; w=wick(n,r)
        kc0=(Ep/c0)**(1/r) if c0>0 else float('nan'); kw=(Ep/w)**(1/r)
        srel=spur/c0 if c0 else float('nan')
        print(f"  r={r}: E_Fp={Ep:>20d} spur={spur:>18d} spur/E_c0={srel:10.6f}  "
              f"K(Fp/c0)={kc0:.4f}  K(Fp/Wick)={kw:.4f}")

print("\n"+"="*100)
print("S6 BETTI DIAGNOSTIC: spur ~ b*p^theta (vary p at fixed n,r; read theta, effective b)")
print("  Deligne predicts: error <= Betti * p^{d-1/2} relative to main p^d -> spur/E_c0 ~ Betti/p^{1/2}")
print("="*100)
for (n,r) in ((16,4),(32,4),(16,5),(32,5)):
    c0=char0_energy_cyclo(n,r)
    print(f"\n--- n={n}, r={r}, E_c0={c0} ---")
    pts=[]
    base=n**4
    for mult in (1,4,16,64,256,1024):
        p=find_prime_1_mod_n(n, base*mult)
        if p>8*10**7: break
        S=mu_n(p,n); Ep=energy_r_charp_fft(p,S,r); spur=Ep-c0; beta=math.log(p)/math.log(n)
        pts.append((p,spur,beta))
        print(f"  p={p:>12d} beta={beta:.3f} spur={spur:>16d}  spur/p={spur/p:.4f}  spur/E_c0={spur/c0:.6e}")
    good=[(p,s) for (p,s,_) in pts if s>0]
    if len(good)>=2:
        print("  spur p-exponent theta + effective Betti b=spur/p^theta:")
        for j in range(1,len(good)):
            theta=(math.log(good[j][1])-math.log(good[j-1][1]))/(math.log(good[j][0])-math.log(good[j-1][0]))
            b=good[j][1]/(good[j][0]**theta)
            print(f"     theta={theta:.3f}  eff_b={b:.4f}  (vs C(2r,r)={math.comb(2*r,r)}, 4^r={4**r})")
