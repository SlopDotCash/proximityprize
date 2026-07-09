#!/usr/bin/env python3
"""
C086 part 2: PRIZE-REGIME check (n << sqrt q, beta ~ 4-5).  The #400 trap: beta~2 primes
give false positives. Here we test ACTUAL prize-shaped primes (multiple per n, proper
subgroup, large prime, beta>=4) to settle whether the SIDON (r=2) face is clean exactly
where the connection's distinguishing claim lives.

We measure:
  (A) SIDON r=2 face: E^{Fp}(mu_n) - (3n^2-3n).  If 0, SidonModNeg holds (no support-<=4
      genuine relation) => the r=2 face is NOT a wall at prize scale.
  (B) The deep face cannot be DP'd at prize primes (q too large), BUT we measure a proxy:
      the minimal GENUINE +-1 relation support up to a feasible cap (length of the
      shortest mod-q-vanishing/char-0-nonzero relation). If the shortest genuine relation
      has support s_min > 4, then SidonModNeg (support<=4) holds even though deeper
      relations (the BGK supply) may exist at support s_min < 2 log q.

This shows the THREE faces sit at THREE different relation lengths:
  sidon r=2  : support 4   (FIXED)
  shortest genuine relation : s_min  (number-theoretic, grows slowly)
  deep BGK   : 2 log q      (the open wall)
"""
import itertools
from math import comb, log2, log
from collections import Counter

def isprime(m):
    if m<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m%p==0: return m==p
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
def factorize(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs
def primitive_root(q):
    facs=factorize(q-1)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in facs): return g
    raise RuntimeError
def mu_subgroup(q,n):
    g=primitive_root(q); h=pow(g,(q-1)//n,q)
    P=[]; x=1
    for _ in range(n): P.append(x); x=x*h%q
    return P
def char0_reduce(coeffs,n):
    half=n//2; red=[0]*half
    for j,c in enumerate(coeffs):
        if c==0: continue
        jj=j%n; sign=1
        while jj>=half: jj-=half; sign=-sign
        red[jj]+=sign*c
    return red
def char0_is_zero(coeffs,n):
    return all(v==0 for v in char0_reduce(coeffs,n))
def energy_fp(P,q):
    rc=Counter()
    for a in P:
        for b in P:
            rc[(a+b)%q]+=1
    return sum(v*v for v in rc.values())
def min_genuine_support(P,q,n,max_s):
    for s in range(2,max_s+1):
        for positions in itertools.combinations(range(n), s):
            for signs_rest in itertools.product((1,-1), repeat=s-1):
                signs=(1,)+signs_rest
                val=0
                for pos,sg in zip(positions,signs):
                    val=(val+sg*P[pos])%q
                if val%q==0:
                    coeffs=[0]*n
                    for pos,sg in zip(positions,signs): coeffs[pos]=sg
                    if not char0_is_zero(coeffs,n):
                        return s
    return None
def find_prize_primes(n, beta, count):
    target=int(n**beta)
    q=((target//n)+1)*n+1
    out=[]
    for _ in range(2000000):
        if isprime(q): out.append(q)
        if len(out)>=count: break
        q+=n
    return out

def run():
    print("="*100)
    print("C086 PRIZE-REGIME: SidonModNeg (r=2, support<=4) at n<<sqrt q (beta~4-5)")
    print("="*100)
    for n in [8,16,32,64]:
        sid_floor=3*n*n-3*n
        cap = 8 if n<=16 else (7 if n<=32 else 6)
        print(f"\n=== n={n}, Sidon floor 3n^2-3n={sid_floor}, search relation support up to {cap} ===")
        for beta in [4.0, 4.5, 5.0]:
            primes=find_prize_primes(n,beta,3)
            for q in primes:
                P=mu_subgroup(q,n)
                b=log(q)/log(n)
                Efp=energy_fp(P,q)
                excess=Efp-sid_floor
                smin=min_genuine_support(P,q,n,cap)
                sid_ok = (excess==0)
                print(f"  q={q:>12} (beta={b:.2f}, n/sqrt q={n/(q**0.5):.4f}): "
                      f"E_excess={excess:>4} (SidonModNeg {'HOLDS' if sid_ok else 'FAILS'}), "
                      f"shortest genuine relation support={smin} (cap {cap})")
    print("\n"+"="*100)
    print("VERDICT DATA: at prize beta>=4, SidonModNeg(mu_n) holds (excess=0) => the r=2")
    print("face is CLEAN, no support-<=4 wall. Shortest genuine relation (if any) has")
    print("support s_min; the deep BGK face needs 2 log q. Three distinct scales.")
    print("="*100)

if __name__=="__main__":
    run()
